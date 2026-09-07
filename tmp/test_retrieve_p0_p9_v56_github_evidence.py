#!/usr/bin/env python3
"""Light metadata tests for the exact P0--P9 v56 retriever."""

from __future__ import annotations

import retrieve_p0_p9_v56_github_evidence as gate


def must_fail(payload: dict[str, object], label: str) -> None:
    try:
        gate.select_artifact(payload)
    except ValueError:
        return
    raise AssertionError(f"{label} did not fail closed")


def main() -> None:
    exact = {
        "artifacts": [
            {"id": 123, "name": gate.EXPECTED_NAME, "expired": False}
        ]
    }
    if gate.select_artifact(exact)["id"] != 123:
        raise AssertionError("exact artifact selection failed")
    must_fail({"artifacts": []}, "missing artifact")
    must_fail(
        {"artifacts": exact["artifacts"] * 2}, "duplicate artifact"
    )
    must_fail(
        {"artifacts": [{"id": 123, "name": gate.EXPECTED_NAME, "expired": True}]},
        "expired artifact",
    )
    print(
        "P0_P9_V56_GITHUB_RETRIEVER_SELFTEST_OK exact=pass "
        "missing=fail_closed duplicate=fail_closed expired=fail_closed"
    )


if __name__ == "__main__":
    main()
