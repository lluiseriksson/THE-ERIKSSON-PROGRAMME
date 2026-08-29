#!/usr/bin/env python3
"""Lightweight synthetic-commit test for the C6d Green owner prefix."""

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
        raise RuntimeError(f"C6D_GREEN_OWNER_PREFIX_TEST_IMPORT_FAILED={path}")
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
            "C6D_GREEN_OWNER_PREFIX_TEST_GIT_FAILED=" + " ".join(args) + "\n"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def main() -> int:
    promotion = load(
        "c6d_green_owner_prefix_promotion_test",
        ROOT / "tmp" / "promote_c6d_green_owner_prefix.py",
    )
    runner_gen = load(
        "c6d_green_owner_prefix_runner_test",
        ROOT / "tmp" / "generate_c6d_green_owner_prefix_runner.py",
    )
    notebook_gen = load(
        "c6d_green_owner_prefix_notebook_test",
        ROOT / "tmp" / "generate_c6d_green_owner_prefix_notebook.py",
    )
    verifier_gen = load(
        "c6d_green_owner_prefix_verifier_test",
        ROOT / "tmp" / "generate_c6d_green_owner_prefix_verifier.py",
    )
    head = git("rev-parse", "HEAD").decode().strip()
    manifest_paths = tuple(
        row.strip()
        for row in (
            ROOT / "tmp" / "c6d-green-owner-prefix-prevalidation-paths.txt"
        ).read_text(encoding="utf-8").splitlines()
        if row.strip()
    )
    promoted_paths = tuple(promotion.destination(relative) for relative in promotion.SOURCES)
    if len(manifest_paths) != 40 or len(set(manifest_paths)) != 40:
        raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_MANIFEST_CARDINALITY")
    if set(manifest_paths) != set(promoted_paths):
        raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_MANIFEST_SCOPE")
    if len(promotion.AUDIT_IMPORTS) != 20:
        raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_CORE_IMPORT_SCOPE")

    with tempfile.TemporaryDirectory(prefix="c6d-green-owner-prefix-") as folder:
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(Path(folder) / "index")
        git("read-tree", head, env=env)
        rows: list[tuple[str, bytes]] = []

        # The real promoter requires these four D2 blobs to exist and be sealed.
        # Synthetic placeholders are sufficient because this test exercises only
        # deterministic transport and runner metadata, never Lean compilation.
        for relative in promotion.PREREQUISITES:
            rows.append((relative, b"-- synthetic sealed D2 prerequisite\n"))
        for relative in promotion.SOURCES:
            data = git("cat-file", "blob", f"{head}:{relative}")
            rows.append((promotion.destination(relative), promotion.promote_text(data)))

        core = git("cat-file", "blob", f"{head}:YangMillsCore.lean").decode()
        if not core.endswith("\n"):
            core += "\n"
        rows.append(("YangMillsCore.lean", (core + "\n".join(promotion.AUDIT_IMPORTS) + "\n").encode()))

        for relative, data in rows:
            oid = git("hash-object", "-w", "--stdin", input_bytes=data).decode().strip()
            git("update-index", "--add", "--cacheinfo", "100644", oid, relative, env=env)
        tree = git("write-tree", env=env).decode().strip()
        source_commit = git(
            "commit-tree", tree, "-p", head,
            input_bytes=b"synthetic C6d Green owner prefix source\n",
        ).decode().strip()

        # Fail before Colab if a promoted module imports another scratch module
        # that the promotion manifest forgot to materialize.  This is a closure
        # check over exact Git blobs, not over the CRLF-sensitive worktree.
        promoted_data = {
            relative: data for relative, data in rows
            if relative.startswith("YangMills/RG/")
        }
        checked_imports = 0
        for relative, data in promoted_data.items():
            for imported in re.findall(
                r"(?m)^import YangMills\.RG\.([A-Za-z0-9_]+)$",
                data.decode(),
            ):
                imported_path = f"YangMills/RG/{imported}.lean"
                git("cat-file", "-e", f"{source_commit}:{imported_path}")
                checked_imports += 1
        if checked_imports == 0:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_IMPORT_CLOSURE_EMPTY")

        runner_text = runner_gen.generate(source_commit)
        compile(runner_text, "synthetic-c6d-green-owner-prefix-runner.py", "exec")
        blobs_match = re.search(
            r"(?ms)^runner\.SOURCE_BLOBS = (\{.*?\})\nrunner\.QUEUE =", runner_text
        )
        queue_match = re.search(
            r"(?ms)^runner\.QUEUE = (\[.*?\])\n\nif __name__", runner_text
        )
        if blobs_match is None:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_SOURCE_BLOBS")
        source_blobs = ast.literal_eval(blobs_match.group(1))
        if set(source_blobs) != set(manifest_paths) | {"YangMillsCore.lean"}:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_SOURCE_BLOB_SCOPE")
        if queue_match is None:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_QUEUE_MISSING")
        queue = ast.literal_eval(queue_match.group(1))
        if len(queue) != 41 or sum(row[2] is not None for row in queue) != 20:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_QUEUE_SCOPE")

        runner_path = Path(folder) / "runner.py"
        runner_path.write_text(runner_text, encoding="utf-8", newline="\n")
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
            input_bytes=b"synthetic C6d Green owner prefix runner\n",
        ).decode().strip()

        notebook_text = notebook_gen.load_base().generate(
            source_commit,
            runner_commit,
            "c6d-green-owner-prefix-v2",
            runner_path=notebook_gen.RUNNER_PATH,
            retain_runtime=True,
        )
        notebook = json.loads(notebook_text)
        cells = [cell for cell in notebook["cells"] if cell.get("cell_type") == "code"]
        if len(cells) != 1:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_NOTEBOOK_CELL_COUNT")
        cell_source = cells[0]["source"]
        compile(
            "".join(cell_source) if isinstance(cell_source, list) else cell_source,
            "synthetic-c6d-green-owner-prefix.ipynb",
            "exec",
        )
        notebook_path = Path(folder) / "notebook.ipynb"
        notebook_path.write_text(notebook_text, encoding="utf-8", newline="\n")
        verifier_text = verifier_gen.generated_text(source_commit, runner_path, notebook_path)
        compile(verifier_text, "synthetic-c6d-green-owner-prefix-verifier.py", "exec")
        if "C6D_GREEN_OWNER_PREFIX_EVIDENCE_OK" not in verifier_text:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_VERIFIER_SENTINEL")
        verifier_queue_match = re.search(
            r"(?m)^QUEUE_STAGES = (\[.*\])$", verifier_text
        )
        if verifier_queue_match is None:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_VERIFIER_QUEUE_MISSING")
        verifier_queue = ast.literal_eval(verifier_queue_match.group(1))
        runner_queue = [row[0] for row in queue]
        if verifier_queue != runner_queue:
            raise RuntimeError(
                "C6D_GREEN_OWNER_PREFIX_TEST_VERIFIER_QUEUE_DIVERGED="
                f"{verifier_queue!r} EXPECTED={runner_queue!r}"
            )
        audit_stages_match = re.search(
            r"(?m)^AUDIT_STAGES = (\{.*\})$", verifier_text
        )
        axiom_headers_match = re.search(
            r"(?m)^EXPECTED_AXIOM_HEADERS = (\{.*\})$", verifier_text
        )
        if audit_stages_match is None or axiom_headers_match is None:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_VERIFIER_AUDIT_MAP_MISSING")
        audit_stages = ast.literal_eval(audit_stages_match.group(1))
        axiom_headers = ast.literal_eval(axiom_headers_match.group(1))
        modules = [module for module, _ in runner_gen.BRICKS]
        expected_audit_stages = {
            module: queue[2 * index + 1][0]
            for index, module in enumerate(modules)
        }
        expected_axiom_headers = {
            module: queue[2 * index + 1][2]
            for index, module in enumerate(modules)
        }
        if audit_stages != expected_audit_stages:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_VERIFIER_AUDIT_MAP_DIVERGED")
        if axiom_headers != expected_axiom_headers:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_TEST_VERIFIER_AXIOM_MAP_DIVERGED")
        print(
            "C6D_GREEN_OWNER_PREFIX_GENERATORS_OK "
            f"synthetic_source={source_commit} source_rows={len(rows)} "
            f"queue={len(queue)} axiom_blocks=24 checked_imports={checked_imports} "
            f"verifier_sha256={hashlib.sha256(verifier_text.encode()).hexdigest().upper()}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
