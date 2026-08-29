#!/usr/bin/env python3
"""Synthetic-commit test for the exact C6d Green value-prefix gate."""

from __future__ import annotations

import ast
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"C6D_VALUE_PREFIX_TEST_IMPORT_FAILED={path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def git(*args: str, input_bytes: bytes | None = None, env=None) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        env=env,
        input=input_bytes,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            "C6D_VALUE_PREFIX_TEST_GIT_FAILED=" + " ".join(args) + "\n"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def main() -> int:
    d2 = load("c6d_value_prefix_d2_test", ROOT / "tmp" / "promote_c6d_exact_green_decay.py")
    promotion = load(
        "c6d_value_prefix_promotion_test",
        ROOT / "tmp" / "promote_c6d_exact_green_value_prefix.py",
    )
    runner_gen = load(
        "c6d_value_prefix_runner_test",
        ROOT / "tmp" / "generate_c6d_exact_green_value_prefix_runner.py",
    )
    notebook_gen = load(
        "c6d_value_prefix_notebook_test",
        ROOT / "tmp" / "generate_c6d_exact_green_value_prefix_notebook.py",
    )
    verifier_gen = load(
        "c6d_value_prefix_verifier_test",
        ROOT / "tmp" / "generate_c6d_exact_green_value_prefix_verifier.py",
    )
    head = git("rev-parse", "HEAD").decode().strip()

    with tempfile.TemporaryDirectory(prefix="c6d-value-prefix-") as folder:
        folder_path = Path(folder)
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(folder_path / "index")
        git("read-tree", head, env=env)
        rows: list[tuple[str, bytes]] = []

        d2_audits: list[str] = []
        for relative in d2.SOURCES:
            data = git("cat-file", "blob", f"{head}:{relative}")
            sealed = d2.promote_text(data).replace(
                b"PRE-VALIDATION:", b"SEALED:", 1
            )
            target = d2.destination(relative)
            rows.append((target, sealed))
            if relative.endswith("Audit.draft.lean"):
                d2_audits.append("import YangMills.RG." + Path(target).stem)

        value_audits: list[str] = []
        for relative in promotion.source_paths():
            data = git("cat-file", "blob", f"{head}:{relative}")
            target = promotion.destination(relative)
            rows.append((target, promotion.promote_text(data)))
            if relative.endswith("Audit.draft.lean"):
                value_audits.append("import YangMills.RG." + Path(target).stem)

        core = git("cat-file", "blob", f"{head}:YangMillsCore.lean").decode()
        if not core.endswith("\n"):
            core += "\n"
        rows.append(
            (
                "YangMillsCore.lean",
                (core + "\n".join(d2_audits + value_audits) + "\n").encode(),
            )
        )

        for relative, data in rows:
            oid = git("hash-object", "-w", "--stdin", input_bytes=data).decode().strip()
            git("update-index", "--add", "--cacheinfo", "100644", oid, relative, env=env)
        tree = git("write-tree", env=env).decode().strip()
        source_commit = git(
            "commit-tree", tree, "-p", head,
            input_bytes=b"synthetic exact C6d value-prefix source\n",
        ).decode().strip()

        runner_text = runner_gen.generate(source_commit)
        compile(runner_text, "synthetic-c6d-value-prefix-runner.py", "exec")
        runner_path = folder_path / "runner.py"
        runner_path.write_text(runner_text, encoding="utf-8", newline="\n")
        blobs_match = re.search(
            r"(?ms)^runner\.SOURCE_BLOBS = (\{.*?\})\nrunner\.QUEUE =", runner_text
        )
        queue_match = re.search(
            r"(?ms)^runner\.QUEUE = (\[.*?\])\n\nif __name__", runner_text
        )
        if blobs_match is None or len(ast.literal_eval(blobs_match.group(1))) != 15:
            raise RuntimeError("C6D_VALUE_PREFIX_TEST_SOURCE_BLOBS")
        if queue_match is None:
            raise RuntimeError("C6D_VALUE_PREFIX_TEST_QUEUE_MISSING")
        queue = ast.literal_eval(queue_match.group(1))
        if len(queue) != 15 or sum(row[2] is not None for row in queue) != 7:
            raise RuntimeError("C6D_VALUE_PREFIX_TEST_QUEUE_SCOPE")

        git("read-tree", source_commit, env=env)
        runner_oid = git(
            "hash-object", "-w", "--stdin", input_bytes=runner_text.encode()
        ).decode().strip()
        git(
            "update-index", "--add", "--cacheinfo", "100644", runner_oid,
            runner_gen.OUTPUT.relative_to(ROOT).as_posix(), env=env,
        )
        runner_tree = git("write-tree", env=env).decode().strip()
        runner_commit = git(
            "commit-tree", runner_tree, "-p", source_commit,
            input_bytes=b"synthetic exact C6d value-prefix runner\n",
        ).decode().strip()

        notebook_text = notebook_gen.load_base().generate(
            source_commit,
            runner_commit,
            "c6d-exact-green-value-prefix-v1",
            runner_path=notebook_gen.RUNNER_PATH,
            retain_runtime=True,
        )
        notebook = json.loads(notebook_text)
        cells = [cell for cell in notebook["cells"] if cell.get("cell_type") == "code"]
        if len(cells) != 1:
            raise RuntimeError("C6D_VALUE_PREFIX_TEST_NOTEBOOK_CELL_COUNT")
        source = cells[0]["source"]
        compile(
            "".join(source) if isinstance(source, list) else source,
            "synthetic-c6d-value-prefix.ipynb",
            "exec",
        )
        notebook_path = folder_path / "notebook.ipynb"
        notebook_path.write_text(notebook_text, encoding="utf-8", newline="\n")

        verifier_text = verifier_gen.generated_text(
            source_commit, runner_path, notebook_path
        )
        compile(verifier_text, "synthetic-c6d-value-prefix-verifier.py", "exec")
        if "C6D_EXACT_GREEN_VALUE_PREFIX_EVIDENCE_OK" not in verifier_text:
            raise RuntimeError("C6D_VALUE_PREFIX_TEST_VERIFIER_SENTINEL")
        print(
            "C6D_EXACT_GREEN_VALUE_PREFIX_GENERATORS_OK "
            f"synthetic_source={source_commit} source_rows={len(rows)} "
            f"verifier_sha256={hashlib.sha256(verifier_text.encode()).hexdigest().upper()}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
