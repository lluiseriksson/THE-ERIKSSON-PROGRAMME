#!/usr/bin/env python3
"""Generate the Step 8b.23 Unit-F Colab validation runner."""

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
EXPECTED_AE_SEALED_DIGEST = (
    "756EC19AAC68AA60B4BB7623ECBFBD0EA833FAF8167DFB211EC87C62AE9621B1"
)
AE_MODULES: tuple[str, ...] = (
    "BalabanCMP89CenteredBrillouinAffineSlice",
    "BalabanCMP89CenteredUnitCubeTorusQuotient",
    "BalabanCMP89CenteredTorusFourierPhase",
    "BalabanCMP89NormalizedBrillouinToTorusMeasure",
    "BalabanCMP89Eq248GreenMassUniformHolomorphy",
    "BalabanCMP89Eq248DisplayedGreenVectorPeriodicity",
    "BalabanCMP89Eq248CenteredGreenTorus",
    "BalabanCMP99CenteredTorusSampleDictionary",
    "BalabanCMP99CenteredTorusPhysicalGreenSampleTransport",
    "BalabanCMP89Eq248GreenOneCoordinateContourShift",
    "BalabanCMP89Eq248GreenProductContourTelescope",
    "BalabanCMP89Eq248MassUniformGreenBound",
    "BalabanCMP89Eq248MassUniformNormalizedGreenBound",
    "BalabanCMP89CenteredTorusGreenCoefficientPhase",
    "BalabanCMP89CenteredTorusGreenCoefficientDictionary",
    "BalabanCMP89SignedLatticeL1TotalSum",
    "BalabanCMP89CenteredGreenFourierSummability",
    "BalabanCMP99PhysicalGreenFiniteGridAliasing",
)
BRICKS: tuple[tuple[str, int], ...] = (
    ("BalabanCMP89CenteredPeriodicL1ResidueSum", 17),
    ("BalabanCMP99CenteredPeriodicEndpointDictionary", 23),
    ("BalabanCMP99PhysicalGreenZeroResidueBound", 3),
    ("BalabanCMP99DiagonalFiniteGreenOwnerBound", 6),
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


def pair_paths(module: str) -> tuple[str, str]:
    stem = f"YangMills/RG/{module}"
    return stem + ".lean", stem + "Audit.lean"


def source_paths() -> tuple[list[str], list[str]]:
    ae = [path for module in AE_MODULES for path in pair_paths(module)]
    unit_f = [path for module, _ in BRICKS for path in pair_paths(module)]
    if len(ae) != 36 or len(unit_f) != 8 or set(ae) & set(unit_f):
        raise RuntimeError("Unit-F validation scope mismatch")
    return ae, unit_f


def q(value: str) -> str:
    return repr(value)


def generate(source_sha: str) -> str:
    resolved = git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved != source_sha:
        raise SystemExit(f"SOURCE_SHA_NOT_FULL_OR_MISMATCH={resolved}")
    ae, unit_f = source_paths()
    rows: list[tuple[str, str]] = []
    prerequisite_rows: list[str] = []
    for path in ae + unit_f:
        data = blob(source_sha, path)
        text = data.decode("utf-8")
        if path in ae and "PRE-VALIDATION:" in text:
            raise SystemExit(f"AE_PREREQUISITE_NOT_SEALED={path}")
        if path in unit_f and "PRE-VALIDATION:" not in text:
            raise SystemExit(f"UNIT_F_MISSING_PRE_VALIDATION={path}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"FORBIDDEN_PLACEHOLDER={path}")
        if re.search(
            r"(?s)/--.*?-/\s*set_option\s+[^\n]+\s+in\s*\n\s*"
            r"(?:set_option\s+[^\n]+\s+in\s*\n\s*)*(?:theorem|lemma)",
            text,
        ):
            raise SystemExit(f"DOCSTRING_BEFORE_SCOPED_OPTION={path}")
        digest = hashlib.sha256(data).hexdigest()
        rows.append((path, digest))
        if path in ae:
            prerequisite_rows.append(f"{digest}  {path}\n")
    prerequisite_digest = hashlib.sha256(
        "".join(prerequisite_rows).encode()
    ).hexdigest().upper()
    if prerequisite_digest != EXPECTED_AE_SEALED_DIGEST:
        raise SystemExit(f"AE_PREREQUISITE_DIGEST_MISMATCH={prerequisite_digest}")
    if sum(count for _, count in BRICKS) != 49:
        raise SystemExit("UNIT_F_AXIOM_TOTAL_MISMATCH")

    blob_rows = "\n".join(f"    {q(path)}: {q(digest)}," for path, digest in rows)
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
"""Colab gate for Step 8b.23 Unit F over sealed A--E prerequisites.

This validates periodic owner decay only.  Regional B0, the independent-scale
dictionary, window 15, terminal fields and TermSource remain open.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
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
spec = importlib.util.spec_from_file_location("step8b23_f_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {{BASE_RUNNER}}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "step8b23-f-v1"
runner.SOURCE_SHA = {q(source_sha)}
runner.ROOT = Path("/content/hrpoly-step8b23-f")
runner.EVIDENCE = Path("/content/hrpoly-step8b23-f-evidence")
runner.ARCHIVE = Path("/content/hrpoly-step8b23-f-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-step8b23-f-paths.txt")
runner.SOURCE_BLOBS = {{
{blob_rows}
}}
runner.QUEUE = [
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
    raise SystemExit(runner.main())
'''


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "scripts" / "colab_step8b23_f_validation.py",
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "STEP8B23_F_RUNNER_GENERATED "
        f"source_sha={args.source_sha} prerequisites=36 unit_f_files=8 "
        f"bricks=4 stages=8 axiom_blocks=49 "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
