#!/usr/bin/env python3
"""Retrieve and independently audit the one terminal P0--P9 v56 artifact."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

import audit_p0_p9_v56_github_evidence as gate


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "lluiseriksson/THE-ERIKSSON-PROGRAMME"
RUN_ID = 32349492939
EXPECTED_HEAD = gate.CONTROL_SHA
EXPECTED_NAME = f"p0-p9-v56-{gate.contract.SOURCE_SHA}"
VERSION_MARKER = "P0_P9_V56"
DESTINATION_SLUG = "p0-p9-v56"


def gh(*args: str, binary: bool = False) -> bytes | str:
    child = subprocess.run(
        ["gh", *args], cwd=ROOT, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, check=False
    )
    if child.returncode:
        raise ValueError(
            "gh failed: " + " ".join(args) + "\n"
            + child.stderr.decode("utf-8", errors="replace")
        )
    if binary:
        return child.stdout
    return child.stdout.decode("utf-8")


def select_artifact(payload: dict[str, object]) -> dict[str, object]:
    artifacts = payload.get("artifacts")
    if not isinstance(artifacts, list):
        raise ValueError("artifact list missing")
    matches = [item for item in artifacts if isinstance(item, dict) and item.get("name") == EXPECTED_NAME]
    if len(matches) != 1:
        raise ValueError(f"exact artifact count={len(matches)}, expected=1")
    artifact = matches[0]
    if artifact.get("expired") is not False or not isinstance(artifact.get("id"), int):
        raise ValueError("artifact expired or id missing")
    return artifact


def main() -> int:
    run = json.loads(
        str(
            gh(
                "run", "view", str(RUN_ID), "--repo", REPOSITORY,
                "--json", "status,conclusion,headSha,url"
            )
        )
    )
    if run != {
        "status": "completed",
        "conclusion": "success",
        "headSha": EXPECTED_HEAD,
        "url": f"https://github.com/{REPOSITORY}/actions/runs/{RUN_ID}",
    }:
        raise SystemExit(f"{VERSION_MARKER}_RUN_NOT_EXACT_SUCCESS={run}")
    listing = json.loads(
        str(
            gh(
                "api",
                f"repos/{REPOSITORY}/actions/runs/{RUN_ID}/artifacts?per_page=100",
            )
        )
    )
    try:
        artifact = select_artifact(listing)
    except ValueError as error:
        raise SystemExit(f"{VERSION_MARKER}_ARTIFACT_METADATA_REJECTED={error}") from error

    destination = ROOT / "validation-evidence" / f"{DESTINATION_SLUG}-run-{RUN_ID}"
    if destination.exists():
        raise SystemExit(f"{VERSION_MARKER}_DESTINATION_EXISTS={destination}")
    destination.mkdir(parents=True)
    artifact_id = int(artifact["id"])
    payload = gh(
        "api", f"repos/{REPOSITORY}/actions/artifacts/{artifact_id}/zip",
        binary=True,
    )
    assert isinstance(payload, bytes)
    archive = destination / "artifact.zip"
    archive.write_bytes(payload)
    measured = hashlib.sha256(payload).hexdigest()
    digest = artifact.get("digest")
    if isinstance(digest, str) and digest.startswith("sha256:"):
        if digest != f"sha256:{measured}":
            raise SystemExit(
                f"{VERSION_MARKER}_GITHUB_DIGEST_MISMATCH={digest}/sha256:{measured}"
            )
    try:
        result = gate.audit(archive)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        raise SystemExit(f"{VERSION_MARKER}_ARTIFACT_REJECTED={error}") from error
    record = {
        "run_id": RUN_ID,
        "run_url": run["url"],
        "control_sha": EXPECTED_HEAD,
        "source_sha": gate.contract.SOURCE_SHA,
        "artifact_id": artifact_id,
        "artifact_name": EXPECTED_NAME,
        "github_digest": digest,
        "outer_zip_sha256": measured.upper(),
        "audit": result,
    }
    (destination / "retrieval.json").write_text(
        json.dumps(record, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )
    print(result)
    print(
        f"{VERSION_MARKER}_GITHUB_RETRIEVAL_OK "
        f"run_id={RUN_ID} artifact_id={artifact_id} "
        f"outer_zip_sha256={measured.upper()} destination={destination}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
