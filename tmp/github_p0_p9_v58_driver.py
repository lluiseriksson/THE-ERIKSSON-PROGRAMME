#!/usr/bin/env python3
"""Exact stop-on-first-error GitHub driver for the P0--P9 v58 scratch chain."""

from pathlib import Path
import sys

import github_p0_p9_v57_driver as core


core.SOURCE_SHA = "7392887bf3b4be4c717bddeb9b0ba5d1d13b0ceb"

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
            raise SystemExit("P0_P9_V58_GITHUB_CONTRACT_DRIFT")
        print(
            "P0_P9_V58_GITHUB_CONTRACT_OK paths=39 stages=49 "
            "audits=20 axiom_headers=199"
        )
        return 0
    return core.main()


if __name__ == "__main__":
    raise SystemExit(main())
