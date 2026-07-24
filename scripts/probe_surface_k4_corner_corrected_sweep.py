"""Point-grid diagnostic for the corrected K4 corner carrier.

The sweep uses midpoint samples only.  It is intentionally not an interval
certificate and cannot promote K4, S1'''/S2''', G2, or G6.
"""

from flint import arb

from surface_remainder_centered_prefactor import dual
from surface_remainder_complement import R_PHYSICAL
from surface_remainder_corner_carrier_design import mirror_coefficient


N = 16
DELTA_LO = arb("0.01")
DELTA_HI = arb("0.0105")
T_VALUES = ("2.9", "1.5", "0.8", "0.589")
NAMES = ("MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror")


def sweep(t_value: str) -> dict[str, arb]:
    side = R_PHYSICAL / DELTA_HI.sqrt()
    width = side / N
    totals = {name: arb(0) for name in NAMES}
    for i in range(N):
        for j in range(N):
            sigma = dual(width * (i + arb("0.5")))
            tau = dual(width * (j + arb("0.5")))
            values = mirror_coefficient(DELTA_LO, arb(t_value), sigma, tau)
            for name in NAMES:
                totals[name] += values[name].c2.v.abs_upper()
    return totals


def main() -> int:
    for t_value in T_VALUES:
        values = sweep(t_value)
        print(t_value, {name: values[name].str(12) for name in NAMES})
    print("SCOPE midpoint diagnostic only; corrected u=(beta*R)^2/4")
    print("NO K4/S1'''/S2'''/G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
