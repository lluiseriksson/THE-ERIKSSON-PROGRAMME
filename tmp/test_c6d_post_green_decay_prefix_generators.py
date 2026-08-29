#!/usr/bin/env python3
"""Lightweight synthetic-commit test for the post-Green D1 gate tools."""

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
        raise RuntimeError(f"C6D_POST_GREEN_TEST_IMPORT_FAILED={path}")
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
            "C6D_POST_GREEN_TEST_GIT_FAILED=" + " ".join(args) + "\n"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def main() -> int:
    promotion = load(
        "c6d_post_green_promotion_test",
        ROOT / "tmp" / "promote_c6d_post_green_decay_prefix.py",
    )
    runner_gen = load(
        "c6d_post_green_runner_test",
        ROOT / "tmp" / "generate_c6d_post_green_decay_prefix_runner.py",
    )
    notebook_gen = load(
        "c6d_post_green_notebook_test",
        ROOT / "tmp" / "generate_c6d_post_green_decay_prefix_notebook.py",
    )
    verifier_gen = load(
        "c6d_post_green_verifier_test",
        ROOT / "tmp" / "generate_c6d_post_green_decay_prefix_verifier.py",
    )
    head = git("rev-parse", "HEAD").decode().strip()

    with tempfile.TemporaryDirectory(prefix="c6d-post-green-") as folder:
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
            for relative in promotion.SOURCES if relative.endswith("Audit.draft.lean")
        ]
        if not core.endswith("\n"):
            core += "\n"
        promoted.append(("YangMillsCore.lean", (core + "\n".join(imports) + "\n").encode()))
        for relative, data in promoted:
            oid = git("hash-object", "-w", "--stdin", input_bytes=data).decode().strip()
            git("update-index", "--add", "--cacheinfo", "100644", oid, relative, env=env)
        tree = git("write-tree", env=env).decode().strip()
        source_commit = git(
            "commit-tree", tree, "-p", head,
            input_bytes=b"synthetic post-Green source\n",
        ).decode().strip()

        runner_text = runner_gen.generate(source_commit)
        compile(runner_text, "synthetic-post-green-runner.py", "exec")
        runner_path = folder_path / "runner.py"
        runner_path.write_text(runner_text, encoding="utf-8", newline="\n")
        blobs = re.search(
            r"(?ms)^runner\.SOURCE_BLOBS = (\{.*?\})\nrunner\.QUEUE =", runner_text
        )
        queue_match = re.search(
            r"(?ms)^runner\.QUEUE = (\[.*?\])\n\nif __name__", runner_text
        )
        if blobs is None or len(ast.literal_eval(blobs.group(1))) != 5:
            raise RuntimeError("C6D_POST_GREEN_TEST_SOURCE_BLOBS")
        if queue_match is None:
            raise RuntimeError("C6D_POST_GREEN_TEST_QUEUE_MISSING")
        queue = ast.literal_eval(queue_match.group(1))
        if len(queue) != 5 or sum(row[2] is not None for row in queue) != 2:
            raise RuntimeError("C6D_POST_GREEN_TEST_QUEUE_SCOPE")

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
            input_bytes=b"synthetic post-Green runner\n",
        ).decode().strip()

        notebook_text = notebook_gen.load_base().generate(
            source_commit,
            runner_commit,
            "c6d-post-green-decay-prefix-v1",
            runner_path=notebook_gen.RUNNER_PATH,
            retain_runtime=True,
        )
        notebook = json.loads(notebook_text)
        cells = [cell for cell in notebook["cells"] if cell.get("cell_type") == "code"]
        if len(cells) != 1:
            raise RuntimeError("C6D_POST_GREEN_TEST_NOTEBOOK_CELL_COUNT")
        source = cells[0]["source"]
        compile("".join(source) if isinstance(source, list) else source, "synthetic.ipynb", "exec")
        notebook_path = folder_path / "notebook.ipynb"
        notebook_path.write_text(notebook_text, encoding="utf-8", newline="\n")

        verifier_text = verifier_gen.generated_text(source_commit, runner_path, notebook_path)
        compile(verifier_text, "synthetic-post-green-verifier.py", "exec")
        if "C6D_POST_GREEN_DECAY_PREFIX_EVIDENCE_OK" not in verifier_text:
            raise RuntimeError("C6D_POST_GREEN_TEST_VERIFIER_SENTINEL")
        print(
            "C6D_POST_GREEN_GENERATORS_OK "
            f"synthetic_source={source_commit} promoted_files={len(promoted)} "
            f"verifier_sha256={hashlib.sha256(verifier_text.encode()).hexdigest().upper()}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
