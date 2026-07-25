"""Unpromoted 160-bit diagnostic wrapper for the current split backend."""

from fractions import Fraction
import certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high_split as base

base.PREC = 160

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    print(base.run(args.unit, Fraction(args.lo), Fraction(args.hi)), end="")

