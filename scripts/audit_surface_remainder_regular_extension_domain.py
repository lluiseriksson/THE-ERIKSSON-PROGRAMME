"""Executable audit for the quarantined regular-extension domain mismatch."""

from fractions import Fraction

import surface_remainder_delta0_extension_cover as regular004
import surface_remainder_delta0_r4_extension_probe as regular005
import surface_remainder_delta0_series_cover_design as sealed


def affected_ranges():
    endpoint = sealed.DELTA_MAX
    candidates = {
        "regular004": regular004.DELTA_MAX,
        "regular005": regular005.DELTA_CANDIDATE,
    }
    return {name: value for name, value in candidates.items()
            if value > endpoint}


def main():
    assert sealed.DELTA_MAX == Fraction(1, 1000)
    affected = affected_ranges()
    assert affected == {
        "regular004": Fraction(1, 250),
        "regular005": Fraction(1, 200),
    }
    print("QUARANTINE CONFIRMED: endpoint outer-domain contract 1/1000; "
          "unparameterized extensions", affected)


if __name__ == "__main__":
    main()
