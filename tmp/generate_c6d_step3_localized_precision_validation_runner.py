#!/usr/bin/env python3
"""Generate the fail-closed Colab runner for the promoted C6d Step3 layer."""

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
PATH_MANIFEST = "tmp/C6D-STEP3-LOCALIZED-PRECISION-PATHS.txt"
REPRO_PATH = "tmp/C6dStep3ContinuousLinearMapEquality.repro.lean"
ROOT_MODULE = "YangMillsCore.lean"
BRICKS: tuple[tuple[str, tuple[str, ...]], ...] = (
    (
        "BalabanCMP99Eq335PhysicalLaplacianInternalCarrier",
        (
            "norm_covariantD0CLM_extendZero_eq_of_eqOn_internalBonds",
            "norm_cmp99ActiveRegionSourceCovariantD0CLM_eq_of_eqOn_internalBonds",
            "cmp99ActiveRegionSourceCovariantLaplacian_eq_of_eqOn_internalBonds",
        ),
    ),
    (
        "BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridge",
        (
            "CMP99Eq335PhysicalRegularityWitness."
            "transformedBackground_eq_exponential_on_internalBonds",
            "CMP99Eq335PhysicalRegularityWitness."
            "regionalLaplacian_eq_exponential_of_sourceRegionDictionary",
        ),
    ),
    (
        "BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision",
        (
            "CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision",
            "CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision_eq",
            "CMP99Eq335PhysicalRegularityClass."
            "localizedRetainedPhysicalPrecision_eq_canonical",
            "CMP99Eq335PhysicalRegularityClass."
            "localizedRetainedPhysicalPrecision_eq_exponentialSource",
            "CMP99Eq335PhysicalRegularityClass."
            "localizedRetainedPhysicalPrecision_isSymmetric",
            "CMP99Eq335PhysicalRegularityClass.inner_localizedRetainedPhysicalPrecision",
        ),
    ),
)
PRINT = re.compile(r"(?m)^#print axioms (?:YangMills\.RG\.)?([^\s]+)\s*$")
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)")
FORBIDDEN = re.compile(r"(?m)^\s*(?:sorry|admit|axiom)\b|\b(?:by\?|exact\?)\b")


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
    if len(paths) != 6 or len(paths) != len(set(paths)):
        raise RuntimeError("C6D_STEP3_VALIDATION_SCOPE_MISMATCH")
    return paths


def q(value: str) -> str:
    return repr(value)


def generate(source_sha: str) -> str:
    resolved = git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved != source_sha:
        raise SystemExit(f"SOURCE_SHA_NOT_FULL_OR_MISMATCH={resolved}")

    paths = source_paths()
    manifest = blob(source_sha, PATH_MANIFEST)
    expected_manifest = "\n".join(paths) + "\n"
    if manifest.decode("utf-8-sig") != expected_manifest:
        raise SystemExit("C6D_STEP3_PATH_MANIFEST_MISMATCH")

    rows: list[tuple[str, str]] = []
    for module, expected in BRICKS:
        source_path, audit_path = pair_paths(module)
        source_data = blob(source_sha, source_path)
        audit_data = blob(source_sha, audit_path)
        for path, data in ((source_path, source_data), (audit_path, audit_data)):
            text = data.decode("utf-8-sig")
            if text.count("PRE-VALIDATION:") != 1:
                raise SystemExit(
                    f"C6D_STEP3_PREVALIDATION_COUNT={path}/"
                    f"{text.count('PRE-VALIDATION:')}"
                )
            if FORBIDDEN.search(text):
                raise SystemExit(f"C6D_STEP3_FORBIDDEN_PLACEHOLDER={path}")
            if re.search(r"(?m)^import\s+tmp\.", text):
                raise SystemExit(f"C6D_STEP3_TMP_IMPORT_SURVIVES={path}")
        actual_imports = IMPORT.findall(audit_data.decode("utf-8-sig"))
        wanted_imports = [f"YangMills.RG.{module}"]
        if actual_imports != wanted_imports:
            raise SystemExit(
                f"C6D_STEP3_AUDIT_IMPORT_MISMATCH={module}/"
                f"{actual_imports!r}"
            )
        actual_prints = PRINT.findall(audit_data.decode("utf-8-sig"))
        if actual_prints != list(expected):
            raise SystemExit(
                f"C6D_STEP3_AUDIT_SCOPE_MISMATCH={module}/"
                f"{actual_prints!r}"
            )
        source_text = source_data.decode("utf-8-sig")
        missing = [name for name in expected if name.rsplit(".", 1)[-1] not in source_text]
        if missing:
            raise SystemExit(f"C6D_STEP3_SOURCE_DECLARATION_MISSING={missing!r}")
        rows.extend(
            (
                (source_path, hashlib.sha256(source_data).hexdigest()),
                (audit_path, hashlib.sha256(audit_data).hexdigest()),
            )
        )

    if sum(len(expected) for _, expected in BRICKS) != 11:
        raise SystemExit("C6D_STEP3_AXIOM_TOTAL_MISMATCH")
    for path, data in (
        (PATH_MANIFEST, manifest),
        (REPRO_PATH, blob(source_sha, REPRO_PATH)),
        (ROOT_MODULE, blob(source_sha, ROOT_MODULE)),
    ):
        rows.append((path, hashlib.sha256(data).hexdigest()))

    blob_rows = "\n".join(f"    {q(path)}: {q(digest)}," for path, digest in rows)
    queue_rows: list[str] = [
        "    (\n"
        "        '00_c6d_step3_clm_extensionality_repro',\n"
        f"        ['lake', 'env', 'lean', {q(REPRO_PATH)}],\n"
        "        None,\n"
        "    ),\n"
        "    (\n"
        "        '00a_c6d_step3_axiom_readout_coverage',\n"
        "        ['python3', 'scripts/check_lean_axiom_readout_coverage.py', "
        f"'--paths-from', {q(PATH_MANIFEST)}],\n"
        "        None,\n"
        "    ),"
    ]
    for index, (module, expected) in enumerate(BRICKS, start=1):
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
            f"        {len(expected)},\n"
            "    ),"
        )
    queue_rows.append(
        "    (\n"
        "        '04_c6d_step3_yang_mills_core_root',\n"
        "        ['lake', 'build', 'YangMillsCore'],\n"
        "        None,\n"
        "    ),"
    )
    queue = "\n".join(queue_rows)

    return f'''#!/usr/bin/env python3
"""Fresh Colab gate for the promoted C6d Step3 localized precision layer.

This runner validates three physical source/audit pairs, all eleven public
axiom readouts, and every repository consumer through ``YangMillsCore``.  It
does not attain window 15, move ``20/41`` or inhabit ``TermSource``.
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
spec = importlib.util.spec_from_file_location("c6d_step3_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {{BASE_RUNNER}}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "c6d-step3-localized-precision-v4"
runner.SOURCE_SHA = {q(source_sha)}
runner.ROOT = Path("/content/hrpoly-c6d-step3-localized-precision")
runner.EVIDENCE = Path("/content/hrpoly-c6d-step3-localized-precision-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-step3-localized-precision-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-step3-localized-precision-paths.txt")
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
        default=ROOT / "scripts" / "colab_c6d_step3_localized_precision_validation.py",
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    compile(content, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "C6D_STEP3_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=9 bricks=3 stages=9 "
        "axiom_blocks=11 root=YangMillsCore "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
