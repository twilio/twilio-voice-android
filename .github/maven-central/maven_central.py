#!/usr/bin/env python3
"""Publish a Voice Android release from Artifactory to Maven Central.

The release on Maven Central is the release in Artifactory `releases`, byte for byte:
the files the Buildkite release build promoted from the QE-validated RC, with their
signatures, downloaded and re-uploaded unchanged (VBLOCKS-7400). Nothing is built or
signed here.

Publishing is two steps, run one after the other. Neither prompts, so they behave the
same in a terminal, a script or an agent:
    python3 local-build-publish/maven_central.py upload 6.10.5 --dry-run   # bundle only
    python3 local-build-publish/maven_central.py upload 6.10.5             # step 1 of 2
    python3 local-build-publish/maven_central.py publish <deployment-id>   # step 2 of 2
    python3 local-build-publish/maven_central.py verify 6.10.5
and, for a deployment:
    python3 local-build-publish/maven_central.py status  <deployment-id>
    python3 local-build-publish/maven_central.py drop    <deployment-id>

`upload` (step 1 of 2) publishes nothing:
  1. Checks the Central credentials, and that X.Y.Z is not on Maven Central already.
  2. Checks Artifactory releases holds exactly the 12 files of a promoted release.
  3. Downloads each file with the .md5, .sha1 and .sha256 Artifactory stores for it,
     and checks the bytes against all three. Using Artifactory's checksums rather than
     computing them here means a download that went wrong cannot slip through.
  4. Verifies the 6 signatures against the release public key committed in
     gradle/release-signing-key.asc, pinned by its fingerprint, with the Gradle task the
     Buildkite promotion uses (verifyPromotedSignatures). The checksums only prove the
     download is intact; this proves the files are the ones signed with the release key.
     It needs no secret and no gpg.
  5. Zips them in Maven repository layout: build/maven-central/X.Y.Z/bundle.zip.
     --dry-run stops here.
  6. Uploads the bundle as a USER_MANAGED deployment, waits for Central to validate
     it, and stops. It prints the deployment id and the `publish` command for step 2.
     Step 2 can also be done in the Central Portal: Publish on the deployment at
     https://central.sonatype.com/publishing/deployments. Drop there, or `drop`,
     discards it instead.
     A VALIDATED deployment can still be dropped.

`publish <deployment-id>` (step 2 of 2) is permanent: a version can never be changed or
removed on Maven Central once it is out.
  1. Checks the deployment is VALIDATED and is com.twilio:voice-android, and logs what
     it will publish.
  2. Publishes, and waits for PUBLISHED, logging the state every minute. For
     6.10.5 that took about 10 minutes. If the wait is interrupted, Central carries on
     publishing; check with `status`.
  3. Waits for all 12 files on repo1.maven.org (up to an hour), logging every minute,
     then runs `verify`. If that wait or check doesn't finish, the release is still
     published: run `verify` later.

Credentials come from the project-root .env used by the other scripts here, or from
the environment:
  MAVEN_CENTRAL_USERNAME / MAVEN_CENTRAL_PASSWORD   a Central Portal *user token*
      (central.sonatype.com > account > Generate User Token), not your Portal login
  MAVEN_ARTIFACTORY_USERNAME / MAVEN_ARTIFACTORY_ACCESS_TOKEN   read access to releases
      (falls back to artifactory.username / artifactory.password in local.properties)
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
import zipfile
from http.client import HTTPException
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
ARTIFACTORY = "https://twilio.jfrog.io/artifactory"
CENTRAL_API = "https://central.sonatype.com/api/v1/publisher"
MAVEN_CENTRAL = "https://repo1.maven.org/maven2"
PORTAL_DEPLOYMENTS = "https://central.sonatype.com/publishing/deployments"
GROUP, ARTIFACT = "com.twilio", "voice-android"
RELEASE_RE = re.compile(r"^\d+\.\d+\.\d+$")
CHECKSUMS = ("md5", "sha1", "sha256")
POLL_SECONDS = 15
PROGRESS_SECONDS = 60
REPO1_WAIT_MINUTES = 60


class Failure(Exception):
    pass


class NetworkFailure(Failure):
    """The connection failed: no HTTP status came back at all."""


def log(message: str) -> None:
    print(f"maven-central: {message}", flush=True)


# --- credentials -----------------------------------------------------------------------


def read_key_values(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    if path.exists():
        for raw in path.read_text().splitlines():
            line = raw.strip()
            if line and not line.startswith("#") and "=" in line:
                key, value = line.split("=", 1)
                values[key.strip()] = value.strip().strip('"').strip("'")
    return values


def credential(dotenv: dict[str, str], name: str) -> str:
    return os.environ.get(name) or dotenv.get(name, "")


def basic(user: str, password: str) -> str:
    return base64.b64encode(f"{user}:{password}".encode()).decode()


# --- HTTP --------------------------------------------------------------------------------


def http(method: str, url: str, auth: str | None = None, data: bytes | None = None,
         headers: dict[str, str] | None = None, timeout: int = 300) -> tuple[int, bytes]:
    request = urllib.request.Request(url, data=data, method=method)
    if auth:
        # Unredirected: Artifactory redirects large downloads to a pre-signed S3 URL,
        # which rejects a request that also carries credentials.
        request.add_unredirected_header("Authorization", auth)
    for key, value in (headers or {}).items():
        request.add_header(key, value)
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            return response.status, response.read()
    except urllib.error.HTTPError as error:
        return error.code, error.read()
    except (urllib.error.URLError, HTTPException, OSError) as error:
        # A dropped or refused TLS connection here has been Zscaler, not the server:
        # retrying didn't help, re-authenticating Zscaler did (6.10.5, 2026-10-19).
        reason = getattr(error, "reason", error)
        host = urllib.parse.urlsplit(url).hostname
        raise NetworkFailure(f"network error talking to {host} ({reason}). Check Zscaler and "
                             "authenticate, then run the command again.") from None


def expected_names(version: str) -> list[str]:
    base = f"{ARTIFACT}-{version}"
    files = [f"{base}.aar", f"{base}-sources.jar", f"{base}-javadoc.jar",
             f"{base}-acknowledgements.md", f"{base}.pom", f"{base}.module"]
    return sorted(files + [name + ".asc" for name in files])


def folder(version: str) -> str:
    return f"{GROUP.replace('.', '/')}/{ARTIFACT}/{version}"


class Artifactory:
    def __init__(self, user: str, password: str, repo: str) -> None:
        if not user or not password:
            raise Failure("no Artifactory credentials: set MAVEN_ARTIFACTORY_USERNAME and "
                          "MAVEN_ARTIFACTORY_ACCESS_TOKEN in .env")
        self.auth = "Basic " + basic(user, password)
        self.repo = repo

    def get(self, path: str) -> tuple[int, bytes]:
        return http("GET", f"{ARTIFACTORY}/{path}", self.auth)

    def storage(self, path: str) -> dict:
        status, body = self.get(f"api/storage/{self.repo}/{path}")
        if status == 404:
            return {}
        if status != 200:
            raise Failure(f"HTTP {status} reading {self.repo}/{path} from Artifactory")
        return json.loads(body)


class Central:
    def __init__(self, user: str, password: str) -> None:
        if not user or not password:
            raise Failure("no Central credentials: set MAVEN_CENTRAL_USERNAME and "
                          "MAVEN_CENTRAL_PASSWORD (a Portal user token) in .env")
        self.auth = "Bearer " + basic(user, password)

    def call(self, method: str, path: str, **kwargs) -> tuple[int, bytes]:
        status, body = http(method, f"{CENTRAL_API}/{path}", self.auth, **kwargs)
        if status in (401, 403):
            raise Failure(
                f"Central rejected the credentials (HTTP {status}). MAVEN_CENTRAL_USERNAME/"
                "PASSWORD must be a Portal user token -- central.sonatype.com > account > "
                "Generate User Token -- with publishing rights on com.twilio. A Portal "
                "login that works in the browser is not one.")
        return status, body

    def is_published(self, version: str) -> bool:
        query = urllib.parse.urlencode({"namespace": GROUP, "name": ARTIFACT, "version": version})
        status, body = self.call("GET", f"published?{query}")
        if status != 200:
            raise Failure(f"HTTP {status} asking Central whether {version} is published: {body[:300]!r}")
        return bool(json.loads(body).get("published"))

    def upload(self, bundle: Path, name: str) -> str:
        boundary = uuid.uuid4().hex
        data = (f"--{boundary}\r\n"
                f'Content-Disposition: form-data; name="bundle"; filename="{bundle.name}"\r\n'
                "Content-Type: application/octet-stream\r\n\r\n").encode()
        data += bundle.read_bytes() + f"\r\n--{boundary}--\r\n".encode()
        query = urllib.parse.urlencode({"name": name, "publishingType": "USER_MANAGED"})
        status, body = self.call("POST", f"upload?{query}", data=data, timeout=1800,
                                 headers={"Content-Type": f"multipart/form-data; boundary={boundary}"})
        if status != 201:
            raise Failure(f"upload failed: HTTP {status}: {body[:500]!r}")
        return body.decode().strip()

    def status(self, deployment: str) -> dict:
        status, body = self.call("POST", f"status?{urllib.parse.urlencode({'id': deployment})}")
        if status != 200:
            raise Failure(f"HTTP {status} reading deployment {deployment}: {body[:300]!r}")
        return json.loads(body)

    def publish(self, deployment: str) -> None:
        status, body = self.call("POST", f"deployment/{deployment}")
        if status != 204:
            raise Failure(f"publish failed: HTTP {status}: {body[:300]!r}")

    def drop(self, deployment: str) -> None:
        status, body = self.call("DELETE", f"deployment/{deployment}")
        if status != 204:
            raise Failure(f"drop failed: HTTP {status}: {body[:300]!r}")


def on_maven_central(version: str) -> bool:
    status, _ = http("HEAD", f"{MAVEN_CENTRAL}/{folder(version)}/{ARTIFACT}-{version}.pom")
    return status == 200


def wait_for_repo1(version: str, timeout_minutes: int) -> None:
    """Wait until all 12 files are on repo1.maven.org, logging every minute."""
    names = expected_names(version)
    start = time.monotonic()
    reported = start
    while True:
        there = sum(http("HEAD", f"{MAVEN_CENTRAL}/{folder(version)}/{n}")[0] == 200 for n in names)
        if there == len(names):
            log(f"all {len(names)} files are on repo1.maven.org")
            return
        now = time.monotonic()
        minutes = int(now - start) // 60
        if minutes >= timeout_minutes:
            raise Failure(f"only {there} of {len(names)} files on repo1.maven.org after "
                          f"{timeout_minutes} minutes")
        if now - reported >= PROGRESS_SECONDS:
            log(f"waiting for repo1.maven.org: {there} of {len(names)} files there after "
                f"{minutes} minute{'' if minutes == 1 else 's'}")
            reported = now
        time.sleep(POLL_SECONDS)


def wait_for(central: Central, deployment: str, wanted: str, timeout_minutes: int) -> dict:
    start = time.monotonic()
    deadline = start + timeout_minutes * 60
    last, reported = None, start
    while True:
        info = central.status(deployment)
        state = info.get("deploymentState")
        if state != last:
            log(f"deployment {deployment}: {state}")
            last, reported = state, time.monotonic()
        elif time.monotonic() - reported >= PROGRESS_SECONDS:
            minutes = int(time.monotonic() - start) // 60
            log(f"deployment {deployment}: still {state} after {minutes} "
                f"minute{'' if minutes == 1 else 's'}")
            reported = time.monotonic()
        if state == wanted:
            return info
        if state == "FAILED":
            errors = json.dumps(info.get("errors", {}), indent=2)
            raise Failure(f"Central rejected the deployment:\n{errors}\n"
                          f"Fix the cause, then `drop {deployment}` and upload again.")
        if time.monotonic() > deadline:
            raise Failure(f"still {state} after {timeout_minutes} minutes; check again with "
                          f"`status {deployment}`")
        time.sleep(POLL_SECONDS)


# --- commands ----------------------------------------------------------------------------


def credentials() -> tuple[dict[str, str], dict[str, str]]:
    return read_key_values(PROJECT_ROOT / ".env"), read_key_values(PROJECT_ROOT / "local.properties")


def artifactory_for(repo: str) -> Artifactory:
    dotenv, local = credentials()
    return Artifactory(
        credential(dotenv, "MAVEN_ARTIFACTORY_USERNAME") or local.get("artifactory.username", ""),
        credential(dotenv, "MAVEN_ARTIFACTORY_ACCESS_TOKEN") or local.get("artifactory.password", ""),
        repo)


def central_client(required: bool = True) -> Central | None:
    dotenv, _ = credentials()
    user = credential(dotenv, "MAVEN_CENTRAL_USERNAME")
    password = credential(dotenv, "MAVEN_CENTRAL_PASSWORD")
    if not required and not (user and password):
        return None
    return Central(user, password)


def fetch_release(artifactory: Artifactory, version: str, work: Path) -> Path:
    """Steps 2 and 3: download and check the release; returns the directory."""
    listing = artifactory.storage(folder(version))
    if not listing:
        raise Failure(f"{artifactory.repo}/{folder(version)} does not exist in Artifactory")
    names = sorted(c["uri"].lstrip("/") for c in listing.get("children", []) if not c.get("folder"))
    expected = expected_names(version)
    if names != expected:
        raise Failure(f"{artifactory.repo}/{folder(version)} is not the expected 12 files; "
                      f"missing {sorted(set(expected) - set(names)) or 'none'}, "
                      f"unexpected {sorted(set(names) - set(expected)) or 'none'}")
    log(f"{artifactory.repo}/{folder(version)}: the 12 expected files")

    aar = f"{folder(version)}/{ARTIFACT}-{version}.aar"
    properties = artifactory.storage(f"{aar}?properties").get("properties", {})
    if artifactory.repo == "releases":
        if not properties.get("promoted.from") or not properties.get("git.commit"):
            raise Failure(f"{aar} has no promoted.from / git.commit property: it was not "
                          "published by the Buildkite release build, so it is not uploaded")
        log(f"promoted from {properties['promoted.from'][0]}, git.commit {properties['git.commit'][0]}")

    files = work / "files"
    files.mkdir(parents=True)
    for name in expected:
        path = f"{artifactory.repo}/{folder(version)}/{name}"
        status, data = artifactory.get(path)
        if status != 200:
            raise Failure(f"HTTP {status} downloading {path}")
        (files / name).write_bytes(data)
        for algorithm in CHECKSUMS:
            status, sidecar = artifactory.get(f"{path}.{algorithm}")
            recorded = sidecar.decode().strip().split()[0] if status == 200 and sidecar.strip() else ""
            if status != 200 or not re.fullmatch(r"[0-9a-f]+", recorded):
                raise Failure(f"Artifactory has no usable {algorithm} for {path} (HTTP {status})")
            if hashlib.new(algorithm, data).hexdigest() != recorded:
                raise Failure(f"{name} does not match its {algorithm} in Artifactory; download again")
            (files / f"{name}.{algorithm}").write_text(recorded)
    log(f"downloaded the 12 files, each matching its {', '.join(CHECKSUMS)} in Artifactory")

    pom = (files / f"{ARTIFACT}-{version}.pom").read_text()
    if f"<version>{version}</version>" not in pom or f"{version}-rc" in pom:
        raise Failure(f"the POM does not declare version {version} cleanly")
    return files


def verify_signatures(files: Path) -> None:
    """Step 4: every signature verifies against the pinned release key."""
    # --console=plain: the progress bar's redraws can overwrite a "good signature" line.
    result = subprocess.run(
        [str(PROJECT_ROOT / "gradlew"), "-q", "--console=plain", f"-Ppromote.dir={files}",
         "verifyPromotedSignatures"],
        cwd=PROJECT_ROOT)
    if result.returncode != 0:
        raise Failure("signature verification failed (see Gradle output above); "
                      "these are not the files signed with the release key")
    log("all 6 signatures verify against the pinned release key")


def build_bundle(files: Path, version: str, work: Path) -> Path:
    """Step 5."""
    bundle = work / "bundle.zip"
    entries = sorted(p.name for p in files.iterdir())
    with zipfile.ZipFile(bundle, "w", zipfile.ZIP_DEFLATED) as archive:
        for name in entries:
            archive.write(files / name, f"{folder(version)}/{name}")
    log(f"bundle: {bundle} ({len(entries)} entries, {bundle.stat().st_size:,} bytes)")
    return bundle


def upload(args: argparse.Namespace) -> None:
    version = args.version
    if not args.dry_run and (not RELEASE_RE.match(version) or args.source_repo != "releases"):
        raise Failure("a real upload takes a release X.Y.Z from releases; --source-repo and "
                      "other versions are for --dry-run tests only")

    # Step 1. A dry run without Central credentials still builds the bundle.
    central = central_client(required=not args.dry_run)
    if central is None:
        log("no Central credentials in .env: skipping the credential check (dry run)")
    elif central.is_published(version):
        raise Failure(f"{GROUP}:{ARTIFACT}:{version} is already published on Maven Central")
    else:
        log(f"Central credentials accepted; {version} is not published yet")
    if on_maven_central(version):
        raise Failure(f"{GROUP}:{ARTIFACT}:{version} is already on repo1.maven.org")

    work = PROJECT_ROOT / "build" / "maven-central" / version
    if work.exists():
        for path in sorted(work.rglob("*"), reverse=True):
            path.unlink() if path.is_file() else path.rmdir()
    work.mkdir(parents=True, exist_ok=True)

    files = fetch_release(artifactory_for(args.source_repo), version, work)
    verify_signatures(files)
    bundle = build_bundle(files, version, work)

    if args.dry_run:
        log("DRY RUN: nothing uploaded. Bundle contents:")
        with zipfile.ZipFile(bundle) as archive:
            for name in archive.namelist():
                print(f"  {name}")
        return

    # Step 6.
    deployment = central.upload(bundle, f"{GROUP}:{ARTIFACT}:{version}")
    (work / "deployment-id").write_text(deployment + "\n")
    log(f"uploaded; deployment id {deployment} (saved in {work / 'deployment-id'})")
    try:
        info = wait_for(central, deployment, "VALIDATED", timeout_minutes=30)
    except NetworkFailure as failure:
        raise Failure(f"{failure} Deployment {deployment} is already uploaded: check it with "
                      f"`python3 {sys.argv[0]} status {deployment}` rather than uploading "
                      "again.") from None
    for purl in info.get("purls", []):
        log(f"validated: {purl}")
    log(f"step 1 of 2 done: deployment {deployment} is VALIDATED. Nothing is published yet.")
    log("step 2 of 2 publishes it to Maven Central, which is permanent and can take tens "
        "of minutes:")
    log(f"  python3 {sys.argv[0]} publish {deployment}")
    log(f"or click Publish on deployment {deployment} at {PORTAL_DEPLOYMENTS}")
    log(f"to discard it instead: python3 {sys.argv[0]} drop {deployment}, or click Drop on "
        f"it at {PORTAL_DEPLOYMENTS}")


def status(args: argparse.Namespace) -> None:
    print(json.dumps(central_client().status(args.deployment), indent=2))


def publish(args: argparse.Namespace) -> None:
    """Step 2 of 2: publish a deployment `upload` left VALIDATED."""
    central, deployment = central_client(), args.deployment
    info = central.status(deployment)
    state, name = info.get("deploymentState"), info.get("deploymentName", "")
    if state != "VALIDATED":
        raise Failure(f"deployment {deployment} is {state}, not VALIDATED")
    if not name.startswith(f"{GROUP}:{ARTIFACT}:"):
        raise Failure(f"deployment {deployment} is {name!r}, not {GROUP}:{ARTIFACT}")
    log(f"step 2 of 2: publishing {name} (deployment {deployment}); this is permanent")
    for purl in info.get("purls", []):
        log(f"  {purl}")
    central.publish(deployment)
    try:
        wait_for(central, deployment, "PUBLISHED", timeout_minutes=90)
    except KeyboardInterrupt:
        raise Failure(f"stopped waiting, but Central carries on publishing; check with "
                      f"`python3 {sys.argv[0]} status {deployment}`") from None
    except NetworkFailure as failure:
        raise Failure(f"{failure} Central carries on publishing regardless: check with "
                      f"`python3 {sys.argv[0]} status {deployment}`, not `publish`.") from None
    version = name.rsplit(":", 1)[1]
    log(f"PUBLISHED {name}. Now waiting for it on repo1.maven.org, then verifying it.")
    try:
        wait_for_repo1(version, timeout_minutes=REPO1_WAIT_MINUTES)
        verify_release(version, "releases")
    except (Failure, KeyboardInterrupt) as failure:
        reason = "stopped waiting" if isinstance(failure, KeyboardInterrupt) else failure
        raise Failure(f"{reason}\n{name} is published; only the check is left. Run it later with "
                      f"`python3 {sys.argv[0]} verify {version}`.") from None


def drop(args: argparse.Namespace) -> None:
    central_client().drop(args.deployment)
    log(f"dropped deployment {args.deployment}")


def verify(args: argparse.Namespace) -> None:
    verify_release(args.version, args.source_repo)


def verify_release(version: str, source_repo: str) -> None:
    """Every file on repo1.maven.org must be byte for byte the file in releases."""
    artifactory = artifactory_for(source_repo)
    mismatches = []
    for name in expected_names(version):
        info = artifactory.storage(f"{folder(version)}/{name}")
        if not info:
            raise Failure(f"{artifactory.repo}/{folder(version)}/{name} is not in Artifactory")
        status, data = http("GET", f"{MAVEN_CENTRAL}/{folder(version)}/{name}")
        if status != 200:
            mismatches.append(f"{name}: HTTP {status} on repo1.maven.org")
        elif hashlib.sha256(data).hexdigest() != info["checksums"]["sha256"]:
            mismatches.append(f"{name}: differs from {artifactory.repo}")
        else:
            log(f"{name}: identical on Maven Central and in {artifactory.repo}")
    if mismatches:
        raise Failure("not verified:\n  " + "\n  ".join(mismatches) +
                      "\n(HTTP 404 right after publishing usually means it has not synced yet)")
    log(f"{GROUP}:{ARTIFACT}:{version} on Maven Central is identical to {artifactory.repo}")
    log(f"https://central.sonatype.com/artifact/{GROUP}/{ARTIFACT}/{version}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    commands = parser.add_subparsers(dest="command", required=True)

    run = commands.add_parser("upload", help="step 1 of 2: upload the release from Artifactory "
                                             "and validate it; publishes nothing")
    run.add_argument("version")
    run.add_argument("--dry-run", action="store_true", help="build the bundle only; upload nothing")
    run.add_argument("--source-repo", default="releases", help=argparse.SUPPRESS)
    run.set_defaults(func=upload)

    for name, func, text in (("status", status, "show a deployment's state"),
                             ("publish", publish, "step 2 of 2: publish a VALIDATED deployment (permanent)"),
                             ("drop", drop, "discard a VALIDATED or FAILED deployment")):
        command = commands.add_parser(name, help=text)
        command.add_argument("deployment")
        command.set_defaults(func=func)

    check = commands.add_parser("verify", help="compare Maven Central with Artifactory releases")
    check.add_argument("version")
    check.add_argument("--source-repo", default="releases", help=argparse.SUPPRESS)
    check.set_defaults(func=verify)

    args = parser.parse_args()
    try:
        args.func(args)
    except Failure as failure:
        print(f"maven-central: ERROR: {failure}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("\nmaven-central: interrupted", file=sys.stderr)
        return 130
    return 0


if __name__ == "__main__":
    sys.exit(main())
