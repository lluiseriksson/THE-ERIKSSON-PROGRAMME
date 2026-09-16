#!/usr/bin/env python3
"""Generate the Step 8b.24 S1--C6b Colab validation runner.

Besides the 17 new source/audit pairs, the exact scope includes the modified
old theorem owner and its unchanged audit.  That old audit must still resolve
all four declarations after the neutral theorem moves to its new module.
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
MOVED_THEOREM = "cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral"
OLD_OWNER = "BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentification"
OLD_OWNER_AUDIT_BLOCKS = 4
BRICKS: tuple[tuple[str, int], ...] = (
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreen", 5),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexification", 4),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier", 6),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionary", 2),
    ("BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral", 1),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentification", 4),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpoint", 4),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrand", 1),
    ("BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction", 4),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpoint", 1),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalZeroResidueAliasing", 4),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceZeroResidue", 1),
    ("BalabanCMP99SourceFineToCoarseCenteredOwnerDictionary", 4),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBound", 2),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalSourceOwnerBound", 1),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceB0", 3),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0", 2),
)
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
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


def source_paths() -> list[str]:
    paths = [path for module, _ in BRICKS for path in pair_paths(module)]
    paths.extend(pair_paths(OLD_OWNER))
    if len(paths) != 36 or len(set(paths)) != 36:
        raise RuntimeError("extension validation scope is not 36 unique paths")
    return paths


def q(value: str) -> str:
    return repr(value)


def generate(source_sha: str) -> str:
    resolved = git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved != source_sha:
        raise SystemExit(f"SOURCE_SHA_NOT_FULL_OR_MISMATCH={resolved}")

    contents: dict[str, bytes] = {}
    digests: list[tuple[str, str]] = []
    new_paths = {path for module, _ in BRICKS for path in pair_paths(module)}
    for path in source_paths():
        data = blob(source_sha, path)
        text = data.decode("utf-8")
        if path in new_paths and "PRE-VALIDATION:" not in text:
            raise SystemExit(f"MISSING_PRE_VALIDATION={path}")
        if path not in new_paths and "PRE-VALIDATION:" in text:
            raise SystemExit(f"OLD_OWNER_UNEXPECTED_PRE_VALIDATION={path}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"FORBIDDEN_PLACEHOLDER={path}")
        contents[path] = data
        digests.append((path, hashlib.sha256(data).hexdigest()))

    neutral_path, _ = pair_paths(BRICKS[4][0])
    old_path, old_audit_path = pair_paths(OLD_OWNER)
    if DECL.findall(contents[neutral_path].decode()).count(MOVED_THEOREM) != 1:
        raise SystemExit("NEUTRAL_OWNER_DOES_NOT_DECLARE_MOVED_THEOREM_ONCE")
    if MOVED_THEOREM in DECL.findall(contents[old_path].decode()):
        raise SystemExit("OLD_OWNER_STILL_DECLARES_MOVED_THEOREM")
    if f"#print axioms YangMills.RG.{MOVED_THEOREM}" not in contents[old_audit_path].decode():
        raise SystemExit("OLD_OWNER_AUDIT_DROPPED_MOVED_THEOREM_READOUT")
    if sum(count for _, count in BRICKS) != 49:
        raise SystemExit("EXTENSION_AXIOM_TOTAL_MISMATCH")

    blob_rows = "\n".join(
        f"    {q(path)}: {q(digest)}," for path, digest in digests
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
        if index == 5:
            queue_rows.append(
                "    (\n"
                "        '05b_old_owner_focal',\n"
                f"        ['lake', 'build', {q('YangMills.RG.' + OLD_OWNER)}],\n"
                "        None,\n"
                "    ),\n"
                "    (\n"
                "        '05b_old_owner_audit',\n"
                "        ['lake', 'env', 'lean', "
                f"{q('YangMills/RG/' + OLD_OWNER + 'Audit.lean')}],\n"
                f"        {OLD_OWNER_AUDIT_BLOCKS},\n"
                "    ),"
            )
    queue = "\n".join(queue_rows)

    return f'''#!/usr/bin/env python3
"""Colab gate for the staged Step 8b.24 S1--C6b extension.

The queue validates 17 new pairs plus the modified old owner/audit pair.
It does not prove a uniform-in-depth B0, attain window 15, discharge a
terminal field or inhabit TermSource.
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
spec = importlib.util.spec_from_file_location("step8b24_extension_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {{BASE_RUNNER}}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "step8b24-extension-v1"
runner.SOURCE_SHA = {q(source_sha)}
runner.ROOT = Path("/content/hrpoly-step8b24-extension")
runner.EVIDENCE = Path("/content/hrpoly-step8b24-extension-evidence")
runner.ARCHIVE = Path("/content/hrpoly-step8b24-extension-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-step8b24-extension-paths.txt")

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
        default=ROOT / "scripts" / "colab_step8b24_extension_validation.py",
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "STEP8B24_EXTENSION_RUNNER_GENERATED "
        f"source_sha={args.source_sha} new_bricks=17 validated_pairs=18 "
        f"files=36 stages=36 axiom_blocks=53 "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
