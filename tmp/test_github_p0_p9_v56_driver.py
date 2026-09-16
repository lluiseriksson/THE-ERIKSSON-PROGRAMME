#!/usr/bin/env python3
"""Light contract and parser tests for the exact P0--P9 GitHub driver."""

from __future__ import annotations

import github_p0_p9_v56_driver as gate


def must_fail(payload: str, expected: int, label: str) -> None:
    try:
        gate.parse_axioms(payload, expected)
    except ValueError:
        return
    raise AssertionError(f"{label} did not fail closed")


def main() -> None:
    paths = gate.exact_paths(gate.Path(__file__).resolve().parents[1])
    stages = gate.queue(paths)
    if len(paths) != 39 or len(stages) != 49:
        raise AssertionError("queue cardinality drift")
    if sum(gate.AXIOM_COUNTS.values()) != 199:
        raise AssertionError("axiom count drift")
    allowed = (
        "a depends on axioms: [propext, Quot.sound]\n"
        "b does not depend on any axioms\n"
    )
    parsed = gate.parse_axioms(allowed, 2)
    if len(parsed) != 2:
        raise AssertionError("allowed parser fixture failed")
    must_fail(allowed, 3, "header count")
    must_fail("a depends on axioms: [sorryAx]\n", 1, "sorryAx")
    must_fail("a depends on axioms: [Classical.choice, extraAx]\n", 1, "extra axiom")
    print(
        "P0_P9_V56_GITHUB_DRIVER_SELFTEST_OK paths=39 stages=49 "
        "audits=20 axiom_headers=199 count_tamper=fail_closed "
        "forbidden_axioms=fail_closed"
    )


if __name__ == "__main__":
    main()
