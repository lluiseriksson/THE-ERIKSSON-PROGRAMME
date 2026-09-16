#!/usr/bin/env python3
"""Light synthetic-commit test for the unified C6d D2 gate."""

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
        raise RuntimeError(f"C6D_D2_OWNER_TEST_IMPORT_FAILED={path}")
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
            "C6D_D2_OWNER_TEST_GIT_FAILED=" + " ".join(args) + "\n"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def main() -> int:
    promotion = load(
        "c6d_d2_owner_promotion_test",
        ROOT / "tmp" / "promote_c6d_exact_green_decay_owner_rescaling.py",
    )
    decay = promotion.load("c6d_d2_owner_decay_promotion", promotion.DECAY_PROMOTER)
    owner = promotion.load("c6d_d2_owner_rescale_promotion", promotion.OWNER_PROMOTER)
    runner_gen = load(
        "c6d_d2_owner_runner_test",
        ROOT / "tmp" / "generate_c6d_exact_green_decay_owner_rescaling_runner.py",
    )
    notebook_gen = load(
        "c6d_d2_owner_notebook_test",
        ROOT / "tmp" / "generate_c6d_exact_green_decay_owner_rescaling_notebook.py",
    )
    verifier_gen = load(
        "c6d_d2_owner_verifier_test",
        ROOT / "tmp" / "generate_c6d_exact_green_decay_owner_rescaling_verifier.py",
    )
    head = git("rev-parse", "HEAD").decode().strip()

    with tempfile.TemporaryDirectory(prefix="c6d-d2-owner-") as folder:
        folder_path = Path(folder)
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(folder_path / "index")
        git("read-tree", head, env=env)
        # The synthetic prerequisite checkpoint models the state immediately
        # before promotion even when this test runs from a later, promoted
        # branch.  Remove only the six generated targets from the temporary
        # index; the real worktree and index remain untouched.
        for relative in (*decay.SOURCES, *owner.SOURCES):
            target = (
                decay.destination(relative)
                if relative in decay.SOURCES
                else owner.destination(relative)
            )
            git("update-index", "--force-remove", "--", target, env=env)
        audit_imports = {
            "import YangMills.RG." + Path(
                decay.destination(relative)
                if relative in decay.SOURCES
                else owner.destination(relative)
            ).stem
            for relative in (*decay.SOURCES, *owner.SOURCES)
            if relative.endswith("Audit.draft.lean")
        }
        core = git("cat-file", "blob", f"{head}:YangMillsCore.lean").decode()
        prepromotion_core = "\n".join(
            line for line in core.splitlines() if line not in audit_imports
        ) + "\n"
        core_oid = git(
            "hash-object", "-w", "--stdin",
            input_bytes=prepromotion_core.encode(),
        ).decode().strip()
        git(
            "update-index", "--add", "--cacheinfo", "100644", core_oid,
            "YangMillsCore.lean", env=env,
        )
        prerequisites = tuple(dict.fromkeys((*decay.PREREQUISITES, *owner.PREREQUISITES)))
        for relative in prerequisites:
            data = git("cat-file", "blob", f"{head}:{relative}")
            if b"PRE-VALIDATION:" not in data:
                continue
            sealed = data.replace(b"PRE-VALIDATION:", b"SEALED:", 1)
            oid = git("hash-object", "-w", "--stdin", input_bytes=sealed).decode().strip()
            git("update-index", "--add", "--cacheinfo", "100644", oid, relative, env=env)
        prerequisite_tree = git("write-tree", env=env).decode().strip()
        prerequisite_commit = git(
            "commit-tree", prerequisite_tree, "-p", head,
            input_bytes=b"synthetic sealed D2 prerequisites\n",
        ).decode().strip()

        promoted = promotion.collect_rows(prerequisite_commit, check_worktree=False)
        for relative, data in promoted:
            oid = git("hash-object", "-w", "--stdin", input_bytes=data).decode().strip()
            git("update-index", "--add", "--cacheinfo", "100644", oid, relative, env=env)
        tree = git("write-tree", env=env).decode().strip()
        source_commit = git(
            "commit-tree", tree, "-p", prerequisite_commit,
            input_bytes=b"synthetic unified C6d D2 source\n",
        ).decode().strip()

        runner_text = runner_gen.generate(source_commit)
        compile(runner_text, "synthetic-c6d-d2-owner-runner.py", "exec")
        runner_path = folder_path / "runner.py"
        runner_path.write_text(runner_text, encoding="utf-8", newline="\n")
        blobs = re.search(r"(?ms)^runner\.SOURCE_BLOBS = (\{.*?\})\nrunner\.QUEUE =", runner_text)
        queue_match = re.search(r"(?ms)^runner\.QUEUE = (\[.*?\])\n\nif __name__", runner_text)
        if blobs is None or len(ast.literal_eval(blobs.group(1))) != 7:
            raise RuntimeError("C6D_D2_OWNER_TEST_SOURCE_BLOBS")
        if queue_match is None:
            raise RuntimeError("C6D_D2_OWNER_TEST_QUEUE_MISSING")
        queue = ast.literal_eval(queue_match.group(1))
        if len(queue) != 7 or sum(row[2] is not None for row in queue) != 3:
            raise RuntimeError("C6D_D2_OWNER_TEST_QUEUE_SCOPE")
        if [row[0] for row in queue].count("04_c6d_d2_owner_rescaling_yang_mills_core_root") != 1:
            raise RuntimeError("C6D_D2_OWNER_TEST_ROOT_SCOPE")

        git("read-tree", source_commit, env=env)
        runner_oid = git("hash-object", "-w", "--stdin", input_bytes=runner_text.encode()).decode().strip()
        git(
            "update-index", "--add", "--cacheinfo", "100644", runner_oid,
            runner_gen.OUTPUT.relative_to(ROOT).as_posix(), env=env,
        )
        runner_tree = git("write-tree", env=env).decode().strip()
        runner_commit = git(
            "commit-tree", runner_tree, "-p", source_commit,
            input_bytes=b"synthetic unified C6d D2 runner\n",
        ).decode().strip()

        notebook_text = notebook_gen.load_base().generate(
            source_commit,
            runner_commit,
            "c6d-d2-owner-rescaling-v2",
            runner_path=notebook_gen.RUNNER_PATH,
            retain_runtime=True,
        )
        notebook = json.loads(notebook_text)
        cells = [cell for cell in notebook["cells"] if cell.get("cell_type") == "code"]
        if len(cells) != 1:
            raise RuntimeError("C6D_D2_OWNER_TEST_NOTEBOOK_CELL_COUNT")
        source = cells[0]["source"]
        compile(
            "".join(source) if isinstance(source, list) else source,
            "synthetic-c6d-d2-owner.ipynb",
            "exec",
        )
        notebook_path = folder_path / "notebook.ipynb"
        notebook_path.write_text(notebook_text, encoding="utf-8", newline="\n")

        verifier_text = verifier_gen.generated_text(source_commit, runner_path, notebook_path)
        compile(verifier_text, "synthetic-c6d-d2-owner-verifier.py", "exec")
        if "C6D_D2_OWNER_RESCALING_EVIDENCE_OK" not in verifier_text:
            raise RuntimeError("C6D_D2_OWNER_TEST_VERIFIER_SENTINEL")
        manifest = ROOT / "tmp" / "c6d-exact-green-decay-owner-rescaling-prevalidation-paths.txt"
        paths = [line for line in manifest.read_text(encoding="utf-8").splitlines() if line]
        if len(paths) != 6 or len(set(paths)) != 6:
            raise RuntimeError("C6D_D2_OWNER_TEST_MANIFEST_SCOPE")
        component_paths: list[str] = []
        for component in (
            ROOT / "tmp" / "c6d-exact-green-decay-prevalidation-paths.txt",
            ROOT / "tmp" / "c6d-owner-decay-rescaling-prevalidation-paths.txt",
        ):
            component_paths.extend(
                line for line in component.read_text(encoding="utf-8").splitlines() if line
            )
        if paths != component_paths:
            raise RuntimeError("C6D_D2_OWNER_TEST_MANIFEST_NOT_EXACT_UNION")
        print(
            "C6D_D2_OWNER_GENERATORS_OK "
            f"synthetic_source={source_commit} promoted_files={len(promoted)} "
            f"verifier_sha256={hashlib.sha256(verifier_text.encode()).hexdigest().upper()}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
