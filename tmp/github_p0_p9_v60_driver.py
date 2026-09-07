#!/usr/bin/env python3
"""Exact stop-on-first-error GitHub driver for the P0--P9 v60 scratch chain."""

import importlib.util
from pathlib import Path
import sys


core_path = Path(__file__).with_name("github_p0_p9_v57_driver.py")
spec = importlib.util.spec_from_file_location("p0_p9_v60_core", core_path)
if spec is None or spec.loader is None:
    raise ImportError(f"cannot load P0-P9 driver core: {core_path}")
core = importlib.util.module_from_spec(spec)
spec.loader.exec_module(core)
core.SOURCE_SHA = "9bcc5b4b2a59e38c2794ebdb9b0791d9b0db6f73"
core.MANIFEST_SHA256 = "04c49992c4ec1d7cb611b978f4754e0758a4ce2aded625d363b768e33ff175a0"

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
        if len(stages) != 49 or sum(AXIOM_COUNTS.values()) != 199:
            raise SystemExit("P0_P9_V60_GITHUB_CONTRACT_DRIFT")
        print(
            "P0_P9_V60_GITHUB_CONTRACT_OK paths=39 stages=49 "
            "audits=20 axiom_headers=199"
        )
        return 0
    return core.main()


if __name__ == "__main__":
    raise SystemExit(main())
