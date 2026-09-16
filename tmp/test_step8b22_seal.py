#!/usr/bin/env python3
"""Synthetic positive/tamper test for the Step 8b.22 mechanical seal."""

from __future__ import annotations

from pathlib import Path
import runpy
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
sys.path.insert(0, str(TMP))
FIXTURE = runpy.run_path(str(TMP / "test_step8b22_cold_evidence.py"))
SEAL = runpy.run_path(str(TMP / "seal_step8b22_from_cold_evidence.py"))


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="step8b22-seal-test-") as raw:
        artifact_root, outer = FIXTURE["make_fixture"](Path(raw))
        result = SEAL["AUDIT"]["validate"](artifact_root, outer)
        plan = SEAL["seal_plan"](result)
        paths = [path.relative_to(ROOT).as_posix() for path, _ in plan]
        assert paths == [
            "YangMills/RG/BalabanCMP99FlatFiniteGridAliasing.lean",
            "YangMills/RG/BalabanCMP99FlatFiniteGridAliasingAudit.lean",
            "YangMillsCore.lean",
            "docs/HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md",
            "docs/VERIFICATION-LEDGER.md",
        ]
        assert SEAL["sha256"](plan[0][1]) == SEAL["SEALED_HASHES"][SEAL["SOURCE"]]
        assert SEAL["sha256"](plan[1][1]) == SEAL["SEALED_HASHES"][SEAL["AUDIT_SOURCE"]]
        assert b"Addendum 867" in plan[-1][1]

        tampered = dict(result)
        tampered["source_sha"] = "0" * 40
        try:
            SEAL["seal_plan"](tampered)
        except SystemExit as error:
            assert "VALIDATED_SOURCE_SHA_MISMATCH" in str(error)
        else:
            raise AssertionError("seal accepted tampered evidence identity")

    print("STEP8B22_SEAL_SELFTEST_OK positive=pass tamper=fail_closed files=5")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
