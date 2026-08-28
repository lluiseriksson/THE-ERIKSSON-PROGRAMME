#!/usr/bin/env python3
"""Generate the fail-closed cold runner for the source-carrier C6d Green."""

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
ROOT_MODULE = "YangMillsCore.lean"
BRICKS = (
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen",
        (
            "cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv",
            "cmp99Eq360C6dSourceSeparatedAmbientRegion",
            "cmp99Eq360C6dSourceSeparatedAmbientRegion_symm_eq",
            "cmp99Eq360C6dSourceSeparatedC6dAmbientPrecision",
            "cmp99Eq360C6dSourceSeparatedAmbientPrecision",
            "cmp99Eq360C6dSourceSeparatedRegionalDirichletPrecision_eq_ambient",
            "isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision",
            "cmp99Eq360C6dSourceSeparatedDirichletPrecision_eq_pullback",
            "cmp99Eq360C6dSourceSeparatedAmbientGreen",
            "cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_ambient",
            "cmp99Eq360C6dSourceSeparatedAmbientPrecision_comp_green",
            "cmp99Eq360C6dSourceSeparatedAmbientGreen_comp_precision",
            "norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_le",
            "cmp99Eq360C6dSourceSeparatedPulledBackC6dGreen",
            "cmp99Eq360C6dSourceSeparatedAmbientGreen_eq_pullback",
        ),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepth",
        (
            "cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity",
            "cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero",
            "isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero",
            "cmp99Eq360C6dSourceSeparatedDirichletPrecision_zero",
            "cmp99Eq360C6dSourceSeparatedRegionalDirichletPrecision_eq_zero",
            "cmp99Eq360C6dSourceSeparatedAmbientGreen_zero",
            "cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_zero",
            "cmp99Eq360C6dSourceSeparatedDirichletPrecision_comp_green_zero",
            "cmp99Eq360C6dSourceSeparatedAmbientGreen_comp_precision_zero",
            "norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_le",
        ),
    ),
)
PRINT = re.compile(r"(?m)^#print axioms (?:YangMills\.RG\.)?([^\s]+)\s*$")
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)")
FORBIDDEN = re.compile(
    r"(?m)^\s*(?:sorry|admit|axiom)\b|\b(?:by\?|exact\?)\b"
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
    return git(  # type: ignore[return-value]
        "cat-file", "blob", f"{source_sha}:{path}", binary=True
    )


def q(value: str) -> str:
    return repr(value)


def generate(source_sha: str) -> str:
    resolved = git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved != source_sha:
        raise SystemExit(f"SOURCE_SHA_NOT_FULL_OR_MISMATCH={resolved}")

    root_data = blob(source_sha, ROOT_MODULE)
    root_text = root_data.decode("utf-8-sig")
    rows: list[tuple[str, str]] = []
    queue_rows: list[str] = []
    for index, (module, declarations) in enumerate(BRICKS, start=1):
        source = f"YangMills/RG/{module}.lean"
        audit = f"YangMills/RG/{module}Audit.lean"
        source_data = blob(source_sha, source)
        audit_data = blob(source_sha, audit)
        source_text = source_data.decode("utf-8-sig")
        audit_text = audit_data.decode("utf-8-sig")
        for path, text in ((source, source_text), (audit, audit_text)):
            if text.count("PRE-VALIDATION:") != 1:
                raise SystemExit(
                    f"C6D_SOURCE_GREEN_PREVALIDATION_COUNT={path}/"
                    f"{text.count('PRE-VALIDATION:')}"
                )
            if FORBIDDEN.search(text):
                raise SystemExit(
                    f"C6D_SOURCE_GREEN_FORBIDDEN_PLACEHOLDER={path}"
                )
            if re.search(r"(?m)^import\s+tmp\.", text):
                raise SystemExit(
                    f"C6D_SOURCE_GREEN_TMP_IMPORT_SURVIVES={path}"
                )
        if IMPORT.findall(audit_text) != [f"YangMills.RG.{module}"]:
            raise SystemExit(
                f"C6D_SOURCE_GREEN_AUDIT_IMPORT_MISMATCH={module}"
            )
        if PRINT.findall(audit_text) != list(declarations):
            raise SystemExit(
                f"C6D_SOURCE_GREEN_AUDIT_SCOPE_MISMATCH={module}/"
                + repr(PRINT.findall(audit_text))
            )
        missing = [name for name in declarations if name not in source_text]
        if missing:
            raise SystemExit(
                f"C6D_SOURCE_GREEN_DECLARATION_MISSING={module}/{missing!r}"
            )
        if f"import YangMills.RG.{module}Audit" not in root_text:
            raise SystemExit(f"C6D_SOURCE_GREEN_ROOT_IMPORT_MISSING={module}")
        rows.extend((
            (source, hashlib.sha256(source_data).hexdigest()),
            (audit, hashlib.sha256(audit_data).hexdigest()),
        ))
        slug = module.removeprefix("Balaban").lower()
        queue_rows.extend((
            "    (\n"
            f"        {q(f'{index:02d}_{slug}_focal')},\n"
            f"        ['lake', 'build', {q('YangMills.RG.' + module)}],\n"
            "        None,\n"
            "    ),",
            "    (\n"
            f"        {q(f'{index:02d}_{slug}_audit')},\n"
            f"        ['lake', 'env', 'lean', {q(audit)}],\n"
            f"        {len(declarations)},\n"
            "    ),",
        ))
    rows.append((ROOT_MODULE, hashlib.sha256(root_data).hexdigest()))
    queue_rows.append(
        "    (\n"
        "        '03_c6d_source_green_yang_mills_core_root',\n"
        "        ['lake', 'build', 'YangMillsCore'],\n"
        "        None,\n"
        "    ),"
    )
    blob_rows = "\n".join(
        f"    {q(path)}: {q(digest)}," for path, digest in rows
    )
    queue = "\n".join(queue_rows)
    return f'''#!/usr/bin/env python3
"""Fresh Colab gate for both source-carrier C6d ambient Green branches.

This runner validates the positive- and zero-depth source/audit pairs, all
twenty-five public axiom readouts and every repository consumer through
``YangMillsCore``.  Passing
does not attain window 15, move ``20/41`` or inhabit ``TermSource``.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
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
spec = importlib.util.spec_from_file_location("c6d_source_green_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {{BASE_RUNNER}}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def streaming_run(stage, command, cwd=None):
    print("STAGE=" + stage + " CMD=" + repr(command), flush=True)
    started = time.perf_counter()
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    stdout_path = runner.EVIDENCE / (
        f"{{len(runner.RECORDS):03d}}-{{stage}}.stdout"
    )
    with stdout_path.open("w", encoding="utf-8", newline="\\n") as stream:
        child = subprocess.Popen(
            command,
            cwd=cwd,
            text=True,
            stdout=stream,
            stderr=subprocess.STDOUT,
        )
        next_heartbeat = started + 30
        while True:
            try:
                returncode = child.wait(timeout=1)
                break
            except subprocess.TimeoutExpired:
                now = time.perf_counter()
                if now >= next_heartbeat:
                    stream.flush()
                    print(
                        "STAGE=" + stage + " HEARTBEAT_SECONDS=%.3f"
                        % (now - started),
                        flush=True,
                    )
                    next_heartbeat = now + 30
    elapsed = time.perf_counter() - started
    output = stdout_path.read_text(encoding="utf-8")
    print(output, flush=True)
    runner.RECORDS.append({{
        "stage": stage,
        "exit": returncode,
        "seconds": elapsed,
        "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
    }})
    print(
        "STAGE=" + stage + " EXIT=" + str(returncode)
        + " SECONDS=%.3f" % elapsed,
        flush=True,
    )
    if returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = streaming_run

runner.RUNNER_REV = "c6d-source-separated-ambient-green-v1"
runner.SOURCE_SHA = {q(source_sha)}
runner.ROOT = Path("/content/hrpoly-c6d-source-separated-ambient-green")
runner.EVIDENCE = Path("/content/hrpoly-c6d-source-separated-ambient-green-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-c6d-source-separated-ambient-green-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-c6d-source-separated-ambient-green-paths.txt"
)
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
        default=(
            ROOT / "scripts"
            / "colab_c6d_source_separated_ambient_green_validation.py"
        ),
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    compile(content, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "C6D_SOURCE_GREEN_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=5 stages=5 "
        f"axiom_blocks={sum(len(ds) for _, ds in BRICKS)} "
        "root=YangMillsCore "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
