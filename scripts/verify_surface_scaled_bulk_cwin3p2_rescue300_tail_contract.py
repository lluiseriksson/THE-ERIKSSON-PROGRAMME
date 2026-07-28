"""Audit the geometric tail contraction for rescue-300 sign transcripts.

This checks the same coefficient/derivative-weight contraction as the
standard CWIN=3/2 tail audit, with the rescue contract's frozen
beta_order=40 and t_order=50 at 300 Arb bits.  It is an analytic dependency
check only; it does not convert sign rows into ``H_tail`` or promote G2/G6.
"""

from fractions import Fraction
from pathlib import Path
import importlib.util

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "scripts" / "verify_surface_scaled_bulk_cwin3p2_high_tail_contract.py"
spec = importlib.util.spec_from_file_location("bulk_tail", BASE)
module = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(module)
module.ORDER = 40
module.WEIGHT_MAX = 52  # rescue t_order 50 + two derivative weights
module.PREC = 300
HEADER = "SCALED BULK SIGN ROW UNIT CWIN3P2 RESCUE300"
MAX_BETA = Fraction(1000, 9)


def parse_domain(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or lines[0] != HEADER:
        return None
    config = next(x for x in lines if x.startswith("config "))
    required = ("CWIN 3/2", "beta_order 40", "t_order 50",
                "min_dt 1/100000", "prec 300")
    if any(token not in config for token in required):
        return None
    fields = next(x for x in lines if x.startswith("beta_domain ")).split()
    lo, hi = Fraction(fields[1]), Fraction(fields[2])
    assert 0 < lo < hi <= MAX_BETA
    return lo, hi


def main() -> int:
    ctx.prec = module.PREC
    paths = []
    for path in sorted((ROOT / "scripts").glob("surface_scaled_bulk*.txt")):
        if path.name.endswith("_rerun.txt") or path.name.endswith(".failed.txt"):
            continue
        parsed = parse_domain(path)
        if parsed is not None:
            paths.append((path, *parsed))
    assert paths, "no rescue-300 production transcripts found"
    global_max = arb(0)
    global_arg = None
    for path, lo, hi in paths:
        coefficient, maximum, arg, k = module.contraction(lo, hi)
        assert coefficient < arb(1) / 2
        assert maximum < arb(1) / 2
        if maximum > global_max:
            global_max, global_arg = maximum, (path.name, lo, hi, arg, k)
        print(path.name, "beta", lo, hi, "k", k,
              "coefficient_ratio", coefficient.str(18),
              "max_derivative_ratio", maximum.str(18), "arg", arg)
    print("SCALED CWIN3P2 RESCUE300 TAIL CONTRACT PASS",
          "units", len(paths), "global_max", global_max.str(24),
          "at", global_arg)
    print("SCOPE analytic tail contraction only; no H_tail/G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
