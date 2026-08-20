#!/usr/bin/env python3
"""Exact stop-on-first-error GitHub driver for the P0--P9 v62 scratch chain."""

import importlib.util
from pathlib import Path
import sys


core_path = Path(__file__).with_name("github_p0_p9_v57_driver.py")
spec = importlib.util.spec_from_file_location("p0_p9_v62_core", core_path)
if spec is None or spec.loader is None:
    raise ImportError(f"cannot load P0-P9 driver core: {core_path}")
core = importlib.util.module_from_spec(spec)
spec.loader.exec_module(core)
core.SOURCE_SHA = "6a8fae8a9581349aa27583a2e6e9e487cac8303e"
core.MANIFEST_SHA256 = "a5506d94e4198a5e6ac5b69dc32e9e1d1bd5b814ea9cf047a428e190c7a111cd"

SOURCE_SHA = core.SOURCE_SHA
MATHLIB_SHA = core.MATHLIB_SHA
AXIOM_COUNTS = core.AXIOM_COUNTS
exact_paths = core.exact_paths
queue = core.queue
parse_axioms = core.parse_axioms


def main() -> int:
    if sys.argv[1:] == ["--contract-only"]:
        paths = exact_paths(Path(__file__).resolve().parents[1])
        stages = queue(paths)
        if len(stages) != 49 or sum(AXIOM_COUNTS.values()) != 200:
            raise SystemExit("P0_P9_V62_GITHUB_CONTRACT_DRIFT")
        print(
            "P0_P9_V62_GITHUB_CONTRACT_OK paths=39 stages=49 "
            "audits=20 axiom_headers=200"
        )
        return 0
    return core.main()


if __name__ == "__main__":
    raise SystemExit(main())
