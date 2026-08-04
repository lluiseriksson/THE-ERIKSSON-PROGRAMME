"""Audit the historical K4 local rows against their actual global judge.

This script promotes no K4 statement.  It makes two previously implicit
facts executable:

* S1''' fractions are additive over a delta partition.
* A transcript label saying PASS is not evidence unless its fractions pass.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
NAMES = (
    "MD2r_mirror",
    "MDFr_mirror",
    "MD_mirror",
    "MF_mirror",
    "muF_main",
    "nuD_main",
    "nuF_main",
)
HISTORICAL_FALSE_GREEN = (
    ROOT / "scripts" / "surface_remainder_k4_tbox_delta0040_t225_230.txt"
)


def tagged_json(lines: list[str], tag: str) -> dict[str, str]:
    prefix = tag + " "
    return json.loads(next(line[len(prefix):]
                           for line in lines if line.startswith(prefix)))


def positive_band_files() -> list[Path]:
    return sorted(
        (ROOT / "scripts").glob(
            "surface_remainder_k4p_??_current_regen.txt"
        )
    )


def audit() -> dict[str, object]:
    ctx.prec = 200
    files = positive_band_files()
    if len(files) != 39:
        raise AssertionError(f"expected 39 current K4 bands, found {len(files)}")

    totals = {name: arb(0) for name in NAMES}
    intervals: list[tuple[Fraction, Fraction]] = []
    for path in files:
        lines = path.read_text(encoding="utf-8").splitlines()
        fractions = tagged_json(lines, "FRACTIONS")
        if set(fractions) != set(NAMES):
            raise AssertionError(f"wrong fraction names in {path.name}")
        for name in NAMES:
            totals[name] += arb(fractions[name])
        config = next(line for line in lines if line.startswith("CONFIG "))
        fields = config.split()
        delta = fields[fields.index("delta") + 1]
        lo, hi = map(Fraction, delta.split(":"))
        intervals.append((lo, hi))

    intervals.sort()
    if intervals[0][0] != Fraction(61, 2000):
        raise AssertionError("positive K4 union has the wrong left endpoint")
    if intervals[-1][1] != Fraction(1, 20):
        raise AssertionError("positive K4 union has the wrong right endpoint")
    for (_, hi), (next_lo, _) in zip(intervals, intervals[1:]):
        if hi != next_lo:
            raise AssertionError(f"positive K4 union gap at {hi}:{next_lo}")

    failed_global_rows = tuple(
        name for name in NAMES if not totals[name].upper() < 1
    )
    expected_failures = {
        "MD2r_mirror", "muF_main", "nuD_main", "nuF_main"
    }
    if set(failed_global_rows) != expected_failures:
        raise AssertionError(
            f"unexpected global K4 verdict set {failed_global_rows}"
        )

    legacy_lines = HISTORICAL_FALSE_GREEN.read_text(
        encoding="utf-8"
    ).splitlines()
    legacy_fractions = tagged_json(legacy_lines, "FRACTIONS")
    legacy_failed = tuple(
        name for name in NAMES if not arb(legacy_fractions[name]).upper() < 1
    )
    if not legacy_failed:
        raise AssertionError("registered false-green witness no longer fails")
    if "K4 CENTERED T-BOX PROBE PASS" not in legacy_lines:
        raise AssertionError("registered false-green terminal is absent")
    config = next(line for line in legacy_lines if line.startswith("CONFIG "))
    if "t 11/5:23/10" not in config:
        raise AssertionError("registered label/domain discrepancy changed")

    # The K4 union begins strictly above the high-beta lane.
    if not Fraction(9, 1000) < intervals[0][0]:
        raise AssertionError("K4/high-beta domain relation changed")

    return {
        "positive_band_count": len(files),
        "positive_delta_union": [
            str(intervals[0][0]), str(intervals[-1][1])
        ],
        "high_beta_delta_max": "9/1000",
        "global_fraction_sums": {
            name: totals[name].str(40) for name in NAMES
        },
        "failed_global_rows": list(failed_global_rows),
        "historical_false_green": str(
            HISTORICAL_FALSE_GREEN.relative_to(ROOT)
        ),
        "historical_failed_rows": list(legacy_failed),
        "historical_executed_t_domain": ["11/5", "23/10"],
    }


def main() -> int:
    result = audit()
    print(json.dumps(result, indent=2, sort_keys=True))
    print("K4 GLOBAL-JUDGE AUDIT PASS: historical local evidence is not "
          "a global S1'''/S2''' certificate")
    print("SCOPE audit/incident only; no K4/G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
