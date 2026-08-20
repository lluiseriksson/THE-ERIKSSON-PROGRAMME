#!/usr/bin/env python3
"""Generate an exact fresh-clone runner for the promoted P0--P9 graph."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

import audit_p0_p5_promotion_preview as preview
import audit_p0_p9_promotion as scope
import audit_p0_p9_v56_evidence as contract


ROOT = Path(__file__).resolve().parents[1]
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bcc852cee5e709bff91fad7de26fa21cff754e1f/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)
P0_P5_PREREQUISITES = (
    "YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge",
    "YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance",
    "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.FinitePiLpTypedKernelReindexAlgebra",
)
P7_P9_PREREQUISITES = (
    "YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.BalabanCMP99SourceGeneratedRegionalFinePartition",
    "YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition",
    "YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas",
    "YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay",
)


def configure_preview() -> None:
    preview.scope = scope
    preview.PATHS = ROOT / "tmp/P0-P9-SCRATCH-PATHS.txt"
    preview.RAW_MANIFEST = ROOT / "tmp/P0-P9-SCRATCH-MANIFEST.sha256"


def git_bytes(*args: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False
    )
    if child.returncode:
        raise SystemExit(
            "GIT_FAIL " + " ".join(args) + "\n"
            + child.stderr.decode("utf-8", errors="replace")
        )
    return child.stdout


def promoted_paths() -> list[str]:
    configure_preview()
    targets = preview.complete_target_map()
    listed = [
        ROOT / line
        for line in preview.PATHS.read_text(encoding="utf-8-sig").splitlines()
        if line
    ]
    if set(listed) != set(targets) or len(listed) != 39:
        raise SystemExit("P0_P9_PROMOTED_RUNNER_SCOPE_DRIFT")
    return [targets[path].relative_to(ROOT).as_posix() for path in listed]


def stage_name(index: int, path: str) -> str:
    stem = Path(path).stem
    return (
        f"p0_p9_promoted_{index:02d}_"
        + re.sub(r"[^A-Za-z0-9]+", "_", stem).lower()
    )


def exact_blobs(source_sha: str, paths: list[str]) -> dict[str, str]:
    result: dict[str, str] = {}
    for path in paths:
        payload = git_bytes("show", f"{source_sha}:{path}")
        result[path] = hashlib.sha256(payload).hexdigest()
    return result


def render(source_sha: str, paths: list[str], blobs: dict[str, str]) -> str:
    audit_counts: dict[str, int] = {}
    configure_preview()
    targets = preview.complete_target_map()
    for scratch, target in targets.items():
        scratch_relative = scratch.relative_to(ROOT).as_posix()
        if scratch_relative in contract.AXIOM_COUNTS:
            audit_counts[target.relative_to(ROOT).as_posix()] = (
                contract.AXIOM_COUNTS[scratch_relative]
            )
    if len(audit_counts) != 20 or sum(audit_counts.values()) != 199:
        raise SystemExit("P0_P9_PROMOTED_AUDIT_CONTRACT_DRIFT")

    queue: list[tuple[str, list[str], int | None]] = [
        (
            "p0_p9_promoted_materialize_project_prerequisites",
            ["lake", "build", *P0_P5_PREREQUISITES],
            None,
        ),
        (
            "p0_p9_promoted_prepare_build_dirs",
            ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
            None,
        ),
    ]
    p7_path = "YangMills/RG/BalabanCMP89SourceSeparatedAmbientPrefixPrecision.lean"
    for index, path in enumerate(paths, start=1):
        if path == p7_path:
            queue.append(
                (
                    "p0_p9_promoted_materialize_p7_p9_project_prerequisites",
                    ["lake", "build", *P7_P9_PREREQUISITES],
                    None,
                )
            )
        command = ["lake", "env", "lean", path]
        if path not in audit_counts:
            command.extend(
                ["-o", f".lake/build/lib/lean/{Path(path).with_suffix('.olean').as_posix()}"]
            )
        queue.append((stage_name(index, path), command, audit_counts.get(path)))

    return f'''#!/usr/bin/env python3
"""Generated fresh-clone gate for the promoted P0--P9 tracked graph."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import urllib.request

SOURCE_SHA = {source_sha!r}
RUNNER_REV = {('p0-p9-promoted-' + source_sha[:12] + '-v1')!r}
BASE_RUNNER_URL = {BASE_RUNNER_URL!r}
BASE_RUNNER_SHA256 = {BASE_RUNNER_SHA256!r}
BASE_RUNNER = Path("/content/colab_qprime_row_validation.py")
SOURCE_BLOBS = {json.dumps(blobs, indent=4, sort_keys=True)}
QUEUE = {repr(queue)}
ALLOWED_AXIOMS = {{"propext", "Classical.choice", "Quot.sound"}}


def fetch_exact(url: str, expected: str) -> bytes:
    with urllib.request.urlopen(url) as response:
        payload = response.read()
    measured = hashlib.sha256(payload).hexdigest()
    print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
    if measured != expected:
        raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
    return payload


BASE_RUNNER.write_bytes(fetch_exact(BASE_RUNNER_URL, BASE_RUNNER_SHA256))
spec = importlib.util.spec_from_file_location("promoted_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load exact base runner")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def parse_axioms(output: str, expected: int) -> None:
    compact = re.sub(r"\\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"dependsonaxioms:\\[([^\\]]*)\\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != expected:
        raise RuntimeError(
            f"AXIOM_HEADER_COUNT={{len(blocks) + pure}} EXPECTED={{expected}}"
        )
    for index, body in enumerate(blocks):
        names = {{name for name in body.split(",") if name}}
        if not names.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET_{{index}}={{sorted(names)}}")


runner.RUNNER_REV = RUNNER_REV
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-p0-p9-promoted")
runner.EVIDENCE = Path("/content/hrpoly-p0-p9-promoted-evidence")
runner.ARCHIVE = Path("/content/hrpoly-p0-p9-promoted-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-p0-p9-promoted-paths.txt")
runner.SOURCE_BLOBS = SOURCE_BLOBS
runner.QUEUE = QUEUE
runner.parse_axioms = parse_axioms


if __name__ == "__main__":
    try:
        from google.colab import runtime
        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    code = runner.main()
    try:
        from google.colab import files
        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(code)
'''


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if re.fullmatch(r"[0-9a-f]{40}", args.source_sha) is None:
        raise SystemExit("SOURCE_SHA_FORMAT_INVALID")
    resolved = git_bytes("rev-parse", f"{args.source_sha}^{{commit}}").decode().strip()
    if resolved != args.source_sha:
        raise SystemExit(f"SOURCE_SHA_NOT_EXACT={resolved}")
    paths = promoted_paths()
    blobs = exact_blobs(args.source_sha, paths)
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    payload = render(args.source_sha, paths, blobs)
    compile(payload, str(output), "exec")
    output.write_text(payload, encoding="utf-8", newline="\n")
    print(
        "P0_P9_PROMOTED_RUNNER_GENERATED "
        f"source_sha={args.source_sha} paths={len(paths)} audits=20 "
        f"axiom_headers=199 sha256={hashlib.sha256(payload.encode()).hexdigest().upper()} "
        f"output={output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
