"""Exact, local-light kill-test for candidate (46).

This is a counterexample harness, not a proof of Birkhoff's theorem.  It uses
only Python's standard library and exact rational arithmetic.  Do not replace
the explicit failures below with ``assert``: optimized Python deletes asserts.
"""

from __future__ import annotations

import itertools
import json
from fractions import Fraction


Matrix = tuple[tuple[Fraction, ...], ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def kronecker(left: Matrix, right: Matrix) -> Matrix:
    return tuple(
        tuple(left[i][j] * right[u][v] for j in range(len(left[0])) for v in range(len(right[0])))
        for i in range(len(left))
        for u in range(len(right))
    )


def cross_ratio_max(matrix: Matrix) -> Fraction:
    rows = range(len(matrix))
    cols = range(len(matrix[0]))
    require(all(matrix[i][j] > 0 for i in rows for j in cols), "matrix must be positive")
    return max(
        matrix[i][k] * matrix[j][ell] / (matrix[i][ell] * matrix[j][k])
        for i, j, k, ell in itertools.product(rows, rows, cols, cols)
    )


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    base: Matrix = (
        (Fraction(3), Fraction(1)),
        (Fraction(1), Fraction(3)),
    )
    tensor = ((Fraction(1),),)
    rows: list[dict[str, object]] = []

    for extent in range(1, 5):
        tensor = kronecker(tensor, base)
        theta = cross_ratio_max(tensor)
        expected_theta = Fraction(9**extent)
        birkhoff = Fraction(3**extent - 1, 3**extent + 1)
        require(theta == expected_theta, f"theta mismatch at L={extent}")
        require(birkhoff >= Fraction(1, 2), f"unexpected contraction at L={extent}")
        rows.append(
            {
                "L": extent,
                "dimension": len(tensor),
                "theta_exact": fraction_text(theta),
                "birkhoff_exact": fraction_text(birkhoff),
                "true_product_spectral_ratio_exact": "1/2",
            }
        )

    require(rows[-1]["birkhoff_exact"] == "40/41", "wall witness did not reach 40/41")
    output = {
        "candidate": 46,
        "status": "KILLED_PROJECTIVE_VOLUME_UNIFORM_BRANCH",
        "arithmetic": "exact Fraction; no floating point",
        "base_theta_exact": "9/1",
        "base_birkhoff_equals_dobrushin_exact": "1/2",
        "rows": rows,
        "verdict": "Delta(K^tensor L)=L Delta(K); global Birkhoff coefficient tends to 1",
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
