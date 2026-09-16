#!/usr/bin/env python3
"""Generate the Colab runner for the H4a/H4b exact endpoint-swap brick."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
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
MODULE = "BalabanCMP89Eq249CompleteHolderEndpointSwap"
AXIOM_BLOCKS = 6


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
    stem = f"YangMills/RG/{MODULE}"
    return [stem + ".lean", stem + "Audit.lean"]


def q(value: str) -> str:
    return repr(value)


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif in_string:
            if text[i] == "\\" and i + 1 < len(text):
                i += 2
            elif text[i] == '"':
                in_string = False
                i += 1
            else:
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            in_string = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or in_string:
        raise SystemExit("H4_SWAP_UNTERMINATED_COMMENT_OR_STRING")
    return "".join(out)


def generate(source_sha: str) -> str:
    resolved = git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved != source_sha:
        raise SystemExit(f"SOURCE_SHA_NOT_FULL_OR_MISMATCH={resolved}")
    rows: list[tuple[str, str]] = []
    for path in source_paths():
        data = blob(source_sha, path)
        text = data.decode("utf-8")
        if text.count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"H4_SWAP_PRE_VALIDATION_COUNT={path}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"FORBIDDEN_PLACEHOLDER={path}")
        rows.append((path, hashlib.sha256(data).hexdigest()))

    source_text = strip_comments_and_strings(
        blob(source_sha, source_paths()[0]).decode("utf-8")
    )
    for forbidden in (
        "holderSeminorm",
        "HolderSeminorm",
        "holderBound",
        "HolderBound",
        "CMP95",
        "CMP96",
        "TermSource",
        "regionalB0",
        "sourceBound",
    ):
        if forbidden in source_text:
            raise SystemExit(f"H4_SWAP_FORBIDDEN_SEMANTIC_TOKEN={forbidden}")

    blob_rows = "\n".join(f"    {q(path)}: {q(digest)}," for path, digest in rows)
    module_target = "YangMills.RG." + MODULE
    audit_target = "YangMills/RG/" + MODULE + "Audit.lean"

    return f'''#!/usr/bin/env python3
"""Colab gate for Step 8b.24 C6c.1 H4a/H4b exact endpoint swap.

This validates only signed-l1 nearest-endpoint selection, exact endpoint
antisymmetry and reconstruction of the original ordered stabilized integrand.
The CMP95 seminorm carrier, source/owner metric dictionary, H4c/H4d, regional
B0, window 15, terminal fields and TermSource remain open.
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
spec = importlib.util.spec_from_file_location("step8b24_c6c1_h4_swap_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {{BASE_RUNNER}}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "step8b24-c6c1-h4-swap-v1"
runner.SOURCE_SHA = {q(source_sha)}
runner.ROOT = Path("/content/hrpoly-step8b24-c6c1-h4-swap")
runner.EVIDENCE = Path("/content/hrpoly-step8b24-c6c1-h4-swap-evidence")
runner.ARCHIVE = Path("/content/hrpoly-step8b24-c6c1-h4-swap-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-step8b24-c6c1-h4-swap-paths.txt")
runner.SOURCE_BLOBS = {{
{blob_rows}
}}
runner.QUEUE = [
    (
        "01_h4_swap_focal",
        ["lake", "build", {q(module_target)}],
        None,
    ),
    (
        "01_h4_swap_audit",
        ["lake", "env", "lean", {q(audit_target)}],
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
        default=ROOT / "scripts" / "colab_step8b24_c6c1_h4_swap_validation.py",
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "STEP8B24_C6C1_H4_SWAP_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=2 bricks=1 stages=2 "
        f"axiom_blocks={AXIOM_BLOCKS} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
