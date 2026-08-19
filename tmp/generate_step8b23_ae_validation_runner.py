#!/usr/bin/env python3
"""Generate the exact Step 8b.23 Units A--E Colab validation runner.

The generator is deliberately Git-object based: every source digest is read
from ``git cat-file blob <source-sha>:<path>`` rather than from the Windows
worktree.  Run it only after the 36 promoted source/audit files have been
committed as one PRE-VALIDATION source checkpoint.

The generated runner compiles all 18 bricks in dependency order and audits
each brick immediately after its focal.  It is stop-on-first-error through the
shared base runner.  Unit F is intentionally absent.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess


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

PERSISTENT_LOG_BLOCK = r'''
def run_with_persistent_log(
    stage: str,
    command: list[str],
    *,
    cwd: Path | None = None,
) -> str:
    """Run one child and retain its complete combined output in evidence."""
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command,
        cwd=cwd,
        env=os.environ.copy(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    output = child.stdout
    print(output, flush=True)
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    log_name = re.sub(r"[^A-Za-z0-9_.-]+", "_", stage) + ".log"
    log_path = runner.EVIDENCE / log_name
    log_path.write_text(output, encoding="utf-8")
    output_hash = hashlib.sha256(output.encode()).hexdigest()
    if hashlib.sha256(log_path.read_bytes()).hexdigest() != output_hash:
        raise RuntimeError("STAGE_LOG_HASH_MISMATCH=" + stage)
    runner.RECORDS.append(
        {
            "stage": stage,
            "exit": child.returncode,
            "seconds": elapsed,
            "output_sha256": output_hash,
            "log": log_name,
        }
    )
    print(
        "STAGE=" + stage + " EXIT=" + str(child.returncode)
        + " SECONDS=%.3f" % elapsed,
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = run_with_persistent_log
'''

# Dependency order and exact public-declaration counts are frozen by
# tmp/audit_step8b23_brick_schedule.py.
BRICKS: tuple[tuple[str, int], ...] = (
    ("BalabanCMP89CenteredBrillouinAffineSlice", 2),
    ("BalabanCMP89CenteredUnitCubeTorusQuotient", 20),
    ("BalabanCMP89CenteredTorusFourierPhase", 4),
    ("BalabanCMP89NormalizedBrillouinToTorusMeasure", 10),
    ("BalabanCMP89Eq248GreenMassUniformHolomorphy", 11),
    ("BalabanCMP89Eq248DisplayedGreenVectorPeriodicity", 4),
    ("BalabanCMP89Eq248CenteredGreenTorus", 8),
    ("BalabanCMP99CenteredTorusSampleDictionary", 5),
    ("BalabanCMP99CenteredTorusPhysicalGreenSampleTransport", 5),
    ("BalabanCMP89Eq248GreenOneCoordinateContourShift", 1),
    ("BalabanCMP89Eq248GreenProductContourTelescope", 5),
    ("BalabanCMP89Eq248MassUniformGreenBound", 12),
    ("BalabanCMP89Eq248MassUniformNormalizedGreenBound", 2),
    ("BalabanCMP89CenteredTorusGreenCoefficientPhase", 5),
    ("BalabanCMP89CenteredTorusGreenCoefficientDictionary", 7),
    ("BalabanCMP89SignedLatticeL1TotalSum", 13),
    ("BalabanCMP89CenteredGreenFourierSummability", 5),
    ("BalabanCMP99PhysicalGreenFiniteGridAliasing", 5),
)
REPROS: tuple[tuple[str, str], ...] = (
    (
        "00_normalized_measure_coefficient_repro",
        "tmp/Step8b23AENormalizedMeasureCoeff.repro.lean",
    ),
    (
        "00b_normalized_measure_full_repro",
        "tmp/Step8b23AENormalizedMeasureFull.repro.lean",
    ),
)


def git(*args: str, binary: bool = False) -> bytes | str:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if child.returncode != 0:
        raise SystemExit(
            "GIT_FAIL " + " ".join(args) + "\n"
            + child.stderr.decode("utf-8", errors="replace")
        )
    return child.stdout if binary else child.stdout.decode("utf-8").strip()


def blob(source_sha: str, path: str) -> bytes:
    return git("cat-file", "blob", f"{source_sha}:{path}", binary=True)  # type: ignore[return-value]


def source_paths() -> list[str]:
    paths: list[str] = []
    for module, _ in BRICKS:
        stem = f"YangMills/RG/{module}"
        paths.extend((stem + ".lean", stem + "Audit.lean"))
    return paths


def q(value: str) -> str:
    return repr(value)


def generate(source_sha: str) -> str:
    resolved = git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved != source_sha:
        raise SystemExit(f"SOURCE_SHA_NOT_FULL_OR_MISMATCH={resolved}")

    digests: list[tuple[str, str]] = []
    for path in source_paths():
        data = blob(source_sha, path)
        text = data.decode("utf-8")
        if "PRE-VALIDATION:" not in text:
            raise SystemExit(f"MISSING_PRE_VALIDATION={path}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"FORBIDDEN_PLACEHOLDER={path}")
        if re.search(
            r"(?s)/--.*?-/\s*set_option\s+[^\n]+\s+in\s*\n\s*"
            r"(?:set_option\s+[^\n]+\s+in\s*\n\s*)*(?:theorem|lemma)",
            text,
        ):
            raise SystemExit(f"DOCSTRING_BEFORE_SCOPED_OPTION={path}")
        digests.append((path, hashlib.sha256(data).hexdigest()))

    repro_digests: list[tuple[str, str]] = []
    for _, repro_path in REPROS:
        repro_data = blob(source_sha, repro_path)
        repro_text = repro_data.decode("utf-8")
        if any(token in repro_text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"FORBIDDEN_PLACEHOLDER={repro_path}")
        if re.search(
            r"(?s)/--.*?-/\s*set_option\s+[^\n]+\s+in\s*\n\s*"
            r"(?:set_option\s+[^\n]+\s+in\s*\n\s*)*(?:theorem|lemma)",
            repro_text,
        ):
            raise SystemExit(f"DOCSTRING_BEFORE_SCOPED_OPTION={repro_path}")
        repro_digests.append((repro_path, hashlib.sha256(repro_data).hexdigest()))
    diagnostic_digests = digests + repro_digests

    if len(digests) != 36 or sum(count for _, count in BRICKS) != 124:
        raise SystemExit("FROZEN_SCOPE_MISMATCH")

    blob_rows = "\n".join(
        f"    {q(path)}: {q(digest)}," for path, digest in diagnostic_digests
    )
    repro_queue = "".join(
        "    (\n"
        f"        {q(stage)},\n"
        f"        [\"lake\", \"env\", \"lean\", {q(path)}],\n"
        "        None,\n"
        "    ),\n"
        for stage, path in REPROS
    )
    queue_rows: list[str] = []
    for index, (module, count) in enumerate(BRICKS, start=1):
        slug = module.removeprefix("Balaban").lower()
        queue_rows.append(
            "    (\n"
            f"        {q(f'{index:02d}_{slug}_focal')},\n"
            f"        ['lake', 'build', {q('YangMills.RG.' + module)}],\n"
            "        None,\n"
            "    ),\n"
            "    (\n"
            f"        {q(f'{index:02d}_{slug}_audit')},\n"
            "        ['lake', 'env', 'lean', "
            f"{q('YangMills/RG/' + module + 'Audit.lean')}],\n"
            f"        {count},\n"
            "    ),"
        )
    queue = "\n".join(queue_rows)

    return f'''#!/usr/bin/env python3
"""Colab gate for Step 8b.23 Units A--E (18 ordered bricks).

The immutable mathematical checkpoint is SOURCE_SHA.  The queue is
stop-on-first-error and audits every focal immediately.  Unit F, regional B0,
window 15, terminal fields and TermSource are outside this runner's scope.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import time
import urllib.request


HERE = Path("/content")
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = {q(BASE_RUNNER_URL)}
BASE_RUNNER_SHA256 = {q(BASE_RUNNER_SHA256)}
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("step8b23_ae_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {{BASE_RUNNER}}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "step8b23-ae-v30"
runner.SOURCE_SHA = {q(source_sha)}
runner.ROOT = Path("/content/hrpoly-step8b23-ae")
runner.EVIDENCE = Path("/content/hrpoly-step8b23-ae-evidence")
runner.ARCHIVE = Path("/content/hrpoly-step8b23-ae-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-step8b23-ae-paths.txt")

runner.SOURCE_BLOBS = {{
{blob_rows}
}}

{PERSISTENT_LOG_BLOCK}
runner.QUEUE = [
{repro_queue}
{queue}
]


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    runner_exit = runner.main()
    try:
        from google.colab import files

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(runner_exit)
'''


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "scripts" / "colab_step8b23_ae_validation.py",
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "STEP8B23_AE_RUNNER_GENERATED "
        f"source_sha={args.source_sha} bricks={len(BRICKS)} "
        f"axiom_blocks={sum(count for _, count in BRICKS)} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
