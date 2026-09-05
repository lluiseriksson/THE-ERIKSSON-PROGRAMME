#!/usr/bin/env python3
"""Lightweight synthetic-commit test for the C6d physical dictionary tools."""

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
        raise RuntimeError(f"C6D_PHYSICAL_DICTIONARY_TEST_IMPORT_FAILED={path}")
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
            "C6D_PHYSICAL_DICTIONARY_TEST_GIT_FAILED="
            + " ".join(args)
            + "\n"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def main() -> int:
    promotion = load(
        "c6d_physical_dictionary_promotion_test",
        ROOT / "tmp" / "promote_c6d_physical_precision_dictionary.py",
    )
    runner_gen = load(
        "c6d_physical_dictionary_runner_test",
        ROOT / "tmp" / "generate_c6d_physical_precision_dictionary_runner.py",
    )
    notebook_gen = load(
        "c6d_physical_dictionary_notebook_test",
        ROOT / "tmp" / "generate_c6d_physical_precision_dictionary_notebook.py",
    )
    verifier_gen = load(
        "c6d_physical_dictionary_verifier_test",
        ROOT / "tmp" / "generate_c6d_physical_precision_dictionary_verifier.py",
    )
    head = git("rev-parse", "HEAD").decode().strip()

    with tempfile.TemporaryDirectory(prefix="c6d-physical-dictionary-") as folder:
        folder_path = Path(folder)
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(folder_path / "index")
        git("read-tree", head, env=env)

        promoted: list[tuple[str, bytes]] = []
        for relative in promotion.SOURCES:
            data = git("cat-file", "blob", f"{head}:{relative}")
            promoted.append((promotion.destination(relative), promotion.promote_text(data)))

        core = git("cat-file", "blob", f"{head}:YangMillsCore.lean").decode()
        imports = [
            "import YangMills.RG." + Path(relative).name.removesuffix(".draft.lean")
            for relative in promotion.SOURCES
            if relative.endswith("Audit.draft.lean")
        ]
        if not core.endswith("\n"):
            core += "\n"
        promoted.append(("YangMillsCore.lean", (core + "\n".join(imports) + "\n").encode()))

        for relative, data in promoted:
            oid = git("hash-object", "-w", "--stdin", input_bytes=data).decode().strip()
            git("update-index", "--add", "--cacheinfo", "100644", oid, relative, env=env)
        tree = git("write-tree", env=env).decode().strip()
        commit = git(
            "commit-tree",
            tree,
            "-p",
            head,
            input_bytes=b"synthetic C6d physical dictionary generator test\n",
        ).decode().strip()

        runner_text = runner_gen.generate(commit)
        compile(runner_text, "synthetic-runner.py", "exec")
        runner_path = folder_path / "runner.py"
        runner_path.write_text(runner_text, encoding="utf-8", newline="\n")
        if runner_text.count("#print axioms") != 0:
            raise RuntimeError("C6D_PHYSICAL_DICTIONARY_TEST_RUNNER_PRINT_TEXT_UNEXPECTED")
        if "axiom_blocks=10" in runner_text:
            raise RuntimeError("C6D_PHYSICAL_DICTIONARY_TEST_GENERATOR_LOG_LEAK")
        source_blobs = re.search(
            r"(?ms)^runner\.SOURCE_BLOBS = (\{.*?\})\nrunner\.QUEUE =", runner_text
        )
        if source_blobs is None or len(ast.literal_eval(source_blobs.group(1))) != 9:
            raise RuntimeError("C6D_PHYSICAL_DICTIONARY_TEST_SOURCE_BLOBS")
        queue_match = re.search(
            r"(?ms)^runner\.QUEUE = (\[.*?\])\n\nif __name__", runner_text
        )
        if queue_match is None:
            raise RuntimeError("C6D_PHYSICAL_DICTIONARY_TEST_QUEUE_MISSING")
        queue = ast.literal_eval(queue_match.group(1))
        if len(queue) != 9 or sum(row[2] is not None for row in queue) != 4:
            raise RuntimeError("C6D_PHYSICAL_DICTIONARY_TEST_AUDIT_STAGE_COUNT")

        git("read-tree", commit, env=env)
        runner_oid = git(
            "hash-object", "-w", "--stdin", input_bytes=runner_text.encode()
        ).decode().strip()
        git(
            "update-index", "--add", "--cacheinfo", "100644", runner_oid,
            runner_gen.OUTPUT.relative_to(ROOT).as_posix(), env=env,
        )
        runner_tree = git("write-tree", env=env).decode().strip()
        runner_commit = git(
            "commit-tree", runner_tree, "-p", commit,
            input_bytes=b"synthetic C6d physical dictionary runner\n",
        ).decode().strip()

        notebook_text = notebook_gen.load_base().generate(
            commit,
            runner_commit,
            "c6d-physical-precision-dictionary-v1",
            runner_path=notebook_gen.RUNNER_PATH,
            retain_runtime=True,
        )
        notebook = json.loads(notebook_text)
        cells = [cell for cell in notebook["cells"] if cell.get("cell_type") == "code"]
        if len(cells) != 1:
            raise RuntimeError("C6D_PHYSICAL_DICTIONARY_TEST_NOTEBOOK_CELL_COUNT")
        source = cells[0]["source"]
        compile("".join(source) if isinstance(source, list) else source, "synthetic.ipynb", "exec")
        notebook_path = folder_path / "notebook.ipynb"
        notebook_path.write_text(notebook_text, encoding="utf-8", newline="\n")

        verifier_text = verifier_gen.generated_text(commit, runner_path, notebook_path)
        compile(verifier_text, "synthetic-verifier.py", "exec")
        if "C6D_PHYSICAL_PRECISION_DICTIONARY_EVIDENCE_OK" not in verifier_text:
            raise RuntimeError("C6D_PHYSICAL_DICTIONARY_TEST_VERIFIER_SENTINEL")
        digest = hashlib.sha256(verifier_text.encode()).hexdigest().upper()
        print(
            "C6D_PHYSICAL_DICTIONARY_GENERATORS_OK "
            f"synthetic_source={commit} promoted_files={len(promoted)} "
            f"verifier_sha256={digest}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
