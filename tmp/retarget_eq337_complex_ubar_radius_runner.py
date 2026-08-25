#!/usr/bin/env python3
"""Retarget the Eq. (3.37) Ubar-radius runner without accepting blob drift."""

from __future__ import annotations

import argparse
import ast
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RUNNER = ROOT / "scripts" / "colab_eq337_complex_ubar_radius_validation.py"


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


def require_commit(sha: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", sha) is None:
        raise SystemExit("SOURCE_SHA_FORMAT_INVALID")
    if git("rev-parse", f"{sha}^{{commit}}") != sha:
        raise SystemExit("SOURCE_SHA_RESOLUTION_MISMATCH")


def source_blobs(tree: ast.Module) -> dict[str, str]:
    matches: list[dict[str, str]] = []
    string_constants: dict[str, str] = {}
    for node in tree.body:
        if (
            isinstance(node, ast.Assign)
            and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str)
        ):
            string_constants[node.targets[0].id] = node.value.value
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            continue
        target = node.targets[0]
        if (
            isinstance(target, ast.Attribute)
            and isinstance(target.value, ast.Name)
            and target.value.id == "runner"
            and target.attr == "SOURCE_BLOBS"
        ):
            if not isinstance(node.value, ast.Dict):
                raise SystemExit("SOURCE_BLOBS_LITERAL_INVALID")
            value: dict[str, str] = {}
            for key_node, digest_node in zip(node.value.keys, node.value.values, strict=True):
                if isinstance(key_node, ast.Constant) and isinstance(key_node.value, str):
                    path = key_node.value
                elif isinstance(key_node, ast.Name) and key_node.id in string_constants:
                    path = string_constants[key_node.id]
                else:
                    raise SystemExit("SOURCE_BLOBS_PATH_NOT_STATIC_TEXT")
                if not (
                    isinstance(digest_node, ast.Constant)
                    and isinstance(digest_node.value, str)
                ):
                    raise SystemExit("SOURCE_BLOBS_DIGEST_NOT_LITERAL_TEXT")
                value[path] = digest_node.value
            matches.append(value)
    if len(matches) != 1:
        raise SystemExit(f"SOURCE_BLOBS_ASSIGNMENT_COUNT={len(matches)} WANT=1")
    return matches[0]


def verify_blobs(source_sha: str, expected: dict[str, str]) -> None:
    mismatches: list[str] = []
    for path, wanted in expected.items():
        blob = git("cat-file", "blob", f"{source_sha}:{path}", binary=True)
        measured = hashlib.sha256(blob).hexdigest()  # type: ignore[arg-type]
        if measured != wanted.lower():
            mismatches.append(f"{path}:{wanted.lower()}:{measured}")
    if mismatches:
        raise SystemExit("SOURCE_BLOB_DRIFT=" + ",".join(mismatches))


def retarget(text: str, source_sha: str, runner_rev: str) -> str:
    tree = ast.parse(text)
    verify_blobs(source_sha, source_blobs(tree))
    source_pattern = re.compile(
        r'(?m)^SOURCE_SHA\s*=\s*["\'][0-9a-f]{40}["\']\s*$'
    )
    revision_pattern = re.compile(
        r'(?m)^runner\.RUNNER_REV\s*=\s*["\'][^"\']+["\']\s*$'
    )
    if len(source_pattern.findall(text)) != 1:
        raise SystemExit("SOURCE_PIN_ASSIGNMENT_COUNT_MISMATCH")
    if len(revision_pattern.findall(text)) != 1:
        raise SystemExit("RUNNER_REV_ASSIGNMENT_COUNT_MISMATCH")
    text = source_pattern.sub(f'SOURCE_SHA = "{source_sha}"', text)
    text = revision_pattern.sub(f'runner.RUNNER_REV = "{runner_rev}"', text)
    compile(text, str(DEFAULT_RUNNER), "exec")
    return text


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--input", type=Path, default=DEFAULT_RUNNER)
    parser.add_argument("--output", type=Path, default=DEFAULT_RUNNER)
    args = parser.parse_args()
    require_commit(args.source_sha)
    content = retarget(args.input.read_text(encoding="utf-8"), args.source_sha, args.runner_rev)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "EQ337_COMPLEX_UBAR_RUNNER_RETARGET_OK "
        f"source_sha={args.source_sha} runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
