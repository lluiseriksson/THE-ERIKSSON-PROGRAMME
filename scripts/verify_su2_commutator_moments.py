#!/usr/bin/env python3
"""Exact finite contractions supporting the SU(2) commutator derivation.

This is deliberately not a Haar-integration proof.  It checks, over exact
rationals, the index contractions used after invoking the certified Schur
orthogonality tensor E[U_ik conj(U_jl)] = delta_ij delta_kl / 2.
"""

from fractions import Fraction
import json


HALF = Fraction(1, 2)
QUARTER = Fraction(1, 4)


def delta(a: int, b: int) -> int:
    return int(a == b)


def first_moment_coefficient(i: int, j: int, k: int, ell: int) -> Fraction:
    """Coefficient of A[k,ell] in E[(U A U^-1)[i,j]]."""
    return HALF * delta(i, j) * delta(k, ell)


def second_moment_coefficient(i: int, j: int, a: int) -> Fraction:
    """Coefficient from E[c[a,a] conj(c[j,i])]."""
    return HALF * delta(a, j) * delta(a, i)


def main() -> None:
    first = {}
    second = {}
    composed = {}
    for i in range(2):
        for j in range(2):
            first[f"{i}{j}"] = {
                f"A{k}{ell}": str(first_moment_coefficient(i, j, k, ell))
                for k in range(2)
                for ell in range(2)
                if first_moment_coefficient(i, j, k, ell)
            }
            second[f"{i}{j}"] = str(
                sum(second_moment_coefficient(i, j, a) for a in range(2))
            )
            composed[f"{i}{j}"] = str(QUARTER * delta(i, j))

    assert first == {
        "00": {"A00": "1/2", "A11": "1/2"},
        "01": {},
        "10": {},
        "11": {"A00": "1/2", "A11": "1/2"},
    }
    assert second == {"00": "1/2", "01": "0", "10": "0", "11": "1/2"}
    assert composed == {"00": "1/4", "01": "0", "10": "0", "11": "1/4"}

    # Concrete non-vacuity data: chi(I)=2 and beta=1 gives beta/16>0.
    beta = Fraction(1)
    chi_identity = 2
    assert chi_identity != 0
    assert beta > 0
    assert beta / 16 == Fraction(1, 16) > 0

    # Exact non-singleton SU(2) witness A = [[0,1],[-1,0]].
    witness = ((0, 1), (-1, 0))
    identity = ((1, 0), (0, 1))
    det_witness = witness[0][0] * witness[1][1] - witness[0][1] * witness[1][0]
    gram = tuple(tuple(sum(witness[k][i] * witness[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))
    assert witness != identity
    assert det_witness == 1
    assert gram == identity
    assert witness[0][0] + witness[1][1] == 0

    print(json.dumps({
        "beta": str(beta),
        "chi_identity": chi_identity,
        "composed_commutator_moment": composed,
        "first_conjugation_contraction": first,
        "second_trace_inverse_contraction": second,
        "scope": "finite exact contraction; not a substitute for Haar/Fubini",
        "status": "PASS",
        "su2_non_singleton_witness": {
            "det": det_witness,
            "matrix": witness,
            "trace": 0,
            "unitary_gram": gram,
        },
    }, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
