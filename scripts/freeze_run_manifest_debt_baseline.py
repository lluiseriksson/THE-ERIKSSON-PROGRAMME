"""Freeze a reviewable run-manifest debt baseline at an exact Git commit."""

from __future__ import annotations

import argparse
import importlib.util
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VALIDATOR_PATH = ROOT / "scripts" / "validate_run_manifests.py"


def _load_validator():
    spec = importlib.util.spec_from_file_location("validate_run_manifests", VALIDATOR_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load validator from {VALIDATOR_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout.strip()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-sha", required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".github" / "run-manifest-debt-baseline.json",
    )
    parser.add_argument("--expected-manifests", type=int, required=True)
    parser.add_argument("--expected-errors", type=int, required=True)
    args = parser.parse_args(argv)

    head = _git("rev-parse", "HEAD")
    if head != args.base_sha:
        raise RuntimeError(f"HEAD {head} does not equal requested base {args.base_sha}")
    changed_manifests = _git("diff", "--name-only", args.base_sha, "--", "run-manifests")
    if changed_manifests:
        raise RuntimeError(
            "run-manifests differ from the requested base; refusing to freeze debt"
        )

    validator = _load_validator()
    baseline = validator.build_debt_baseline(
        root=ROOT,
        manifest_dir=ROOT / "run-manifests",
        base_sha=args.base_sha,
    )
    if baseline["manifest_count"] != args.expected_manifests:
        raise RuntimeError(
            f"expected {args.expected_manifests} manifests, got "
            f"{baseline['manifest_count']}"
        )
    if baseline["strict_error_count"] != args.expected_errors:
        raise RuntimeError(
            f"expected {args.expected_errors} errors, got "
            f"{baseline['strict_error_count']}"
        )

    output = args.output if args.output.is_absolute() else ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(baseline, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        f"froze {baseline['manifest_count']} manifests and "
        f"{baseline['strict_error_count']} strict errors at {args.base_sha} in {output}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
