"""Validate production/replay for the scoped K4 t-box [2.9,2.91]."""

from pathlib import Path
from flint import arb

ROOT = Path(__file__).resolve().parents[1]
PROD = ROOT / "scripts" / "surface_remainder_k4_tbox_290_291.txt"
REPLAY = ROOT / "scripts" / "surface_remainder_k4_tbox_290_291_rerun.txt"


def parse(path):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "K4 ENDPOINT TBOX 290_291"
    assert lines[5].startswith("t_domain ")
    assert "K4 ENDPOINT TBOX 290_291 PASS" in lines
    assert "SCOPE t=[2.9,2.91] only; delta [0.048,0.05]; no global K4 theorem claim" in lines
    segments = [line for line in lines if line.startswith("segment ")]
    assert segments == [
        "segment 0 delta 0.048 0.049 cells 2304 fallbacks 142",
        "segment 1 delta 0.049 0.05 cells 1152 fallbacks 103",
    ]
    totals = {line.split()[1]: arb(line.split(maxsplit=2)[2])
              for line in lines if line.startswith("total_fraction ")}
    assert set(totals) == {"MD_mirror", "MF_mirror", "MD2r_mirror",
                           "MDFr_mirror", "muF_main", "nuD_main", "nuF_main"}
    assert all(v.is_finite() and v.upper() < 1 for v in totals.values())
    return lines


def main():
    assert parse(PROD) == parse(REPLAY)
    print("K4 TBOX 290_291 VALIDATION PASS: production/replay byte equal")


if __name__ == "__main__":
    main()
