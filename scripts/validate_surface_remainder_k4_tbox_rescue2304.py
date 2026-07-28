"""Validate a production/replay pair for the scoped 2,304-cell rescue."""

import argparse
from pathlib import Path
from flint import arb

ROOT = Path(__file__).resolve().parents[1]


def parse(path, unit, t_lo, t_hi):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == f"K4 ENDPOINT TBOX RESCUE2304 {unit}"
    assert lines[5].startswith(f"t_domain {t_lo} {t_hi} ")
    assert f"K4 ENDPOINT TBOX RESCUE2304 {unit} PASS" in lines
    assert (f"SCOPE t=[{t_lo},{t_hi}] only; delta [0.048,0.05]; "
            "no global K4 theorem claim") in lines
    segments = [line for line in lines if line.startswith("segment ")]
    assert len(segments) == 2
    assert segments[0].startswith("segment 0 delta 0.048 0.049 cells 2304")
    assert segments[1].startswith("segment 1 delta 0.049 0.05 cells 2304")
    totals = {line.split()[1]: arb(line.split(maxsplit=2)[2])
              for line in lines if line.startswith("total_fraction ")}
    expected = {"MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror",
                "muF_main", "nuD_main", "nuF_main"}
    assert set(totals) == expected
    assert all(v.is_finite() and v.upper() < 1 for v in totals.values())
    return lines


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--t-lo", required=True)
    parser.add_argument("--t-hi", required=True)
    args = parser.parse_args()
    prod = ROOT / "scripts" / f"surface_remainder_k4_tbox_rescue2304_{args.unit}.txt"
    replay = ROOT / "scripts" / f"surface_remainder_k4_tbox_rescue2304_{args.unit}_rerun.txt"
    assert parse(prod, args.unit, args.t_lo, args.t_hi) == parse(
        replay, args.unit, args.t_lo, args.t_hi)
    print("K4 RESCUE2304 VALIDATION PASS", args.unit,
          "production/replay byte equal")

