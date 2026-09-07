#!/usr/bin/env python3
"""Generate the first-error Colab runner for the promoted C6c.2 P0 pair."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
MODULE = "BalabanCMP99SourceCanonicalPrefixTower"
AXIOM_BLOCKS = 10
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bcc852cee5e709bff91fad7de26fa21cff754e1f/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)
PRINT = re.compile(r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_.'’]+)")
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)")


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
            "GIT_FAIL "
            + " ".join(args)
            + "\n"
            + child.stderr.decode("utf-8", errors="replace")
        )
    return child.stdout if binary else child.stdout.decode("utf-8").strip()


def blob(source_sha: str, path: str) -> bytes:
    return git("cat-file", "blob", f"{source_sha}:{path}", binary=True)  # type: ignore[return-value]


def q(value: str) -> str:
    return repr(value)


def generate(source_sha: str) -> str:
    resolved = git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved != source_sha:
        raise SystemExit(f"SOURCE_SHA_NOT_FULL_OR_MISMATCH={resolved}")
    source_path = f"YangMills/RG/{MODULE}.lean"
    audit_path = f"YangMills/RG/{MODULE}Audit.lean"
    source = blob(source_sha, source_path)
    audit = blob(source_sha, audit_path)
    texts = {
        source_path: source.decode("utf-8"),
        audit_path: audit.decode("utf-8"),
    }
    for path, text in texts.items():
        if text.count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"P0_PRE_VALIDATION_COUNT={path}/{text.count('PRE-VALIDATION:')}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"P0_FORBIDDEN_PLACEHOLDER={path}")
        if re.search(r"(?m)^import\s+tmp\.", text):
            raise SystemExit(f"P0_TMP_IMPORT_SURVIVES={path}")

    declarations = DECL.findall(texts[source_path])
    prints = PRINT.findall(texts[audit_path])
    if len(declarations) != AXIOM_BLOCKS:
        raise SystemExit(
            f"P0_DECLARATION_COUNT={len(declarations)}/{AXIOM_BLOCKS}"
        )
    if prints != declarations:
        raise SystemExit(
            f"P0_AUDIT_ORDER_SCOPE_MISMATCH expected={declarations} actual={prints}"
        )
    expected_import = [f"YangMills.RG.{MODULE}"]
    actual_import = IMPORT.findall(texts[audit_path])
    if actual_import != expected_import:
        raise SystemExit(
            f"P0_AUDIT_IMPORT_MISMATCH expected={expected_import} actual={actual_import}"
        )

    source_hash = hashlib.sha256(source).hexdigest()
    audit_hash = hashlib.sha256(audit).hexdigest()
    return f'''#!/usr/bin/env python3
"""Colab first-error diagnostic for Step 8b.24/C6c.2 P0 only.

This runner validates the canonical retained-prefix construction and its exact
ten-readout sibling audit.  It does not introduce P1--P5, attain window 15,
move a terminal counter or inhabit TermSource.
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
spec = importlib.util.spec_from_file_location("step8b24_c6c2_p0_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {{BASE_RUNNER}}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "step8b24-c6c2-p0-v1"
runner.SOURCE_SHA = {q(source_sha)}
runner.ROOT = Path("/content/hrpoly-step8b24-c6c2-p0")
runner.EVIDENCE = Path("/content/hrpoly-step8b24-c6c2-p0-evidence")
runner.ARCHIVE = Path("/content/hrpoly-step8b24-c6c2-p0-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-step8b24-c6c2-p0-paths.txt")
runner.SOURCE_BLOBS = {{
    {q(source_path)}: {q(source_hash)},
    {q(audit_path)}: {q(audit_hash)},
}}
runner.QUEUE = [
    (
        "01_p0_canonical_prefix_tower_focal",
        ["lake", "build", {q('YangMills.RG.' + MODULE)}],
        None,
    ),
    (
        "02_p0_canonical_prefix_tower_audit",
        ["lake", "env", "lean", {q(audit_path)}],
        {AXIOM_BLOCKS},
    ),
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
        default=ROOT / "scripts" / "colab_step8b24_c6c2_p0_validation.py",
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    compile(content, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "STEP8B24_C6C2_P0_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=2 bricks=1 stages=2 "
        f"axiom_blocks={AXIOM_BLOCKS} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
