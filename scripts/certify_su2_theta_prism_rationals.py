#!/usr/bin/env python3
"""Independent exact-rational replay for (9) Fabricante del prisma theta."""

from fractions import Fraction
import json


def q(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


three_branch_rank = 3 + 1 - 2
reduced_rank = 2 + 1 - 2
singlet = Fraction(1, 2)
norm_sq = (
    Fraction(1)
    - singlet * Fraction(1, 2)
    - singlet * Fraction(1, 2)
    + singlet * singlet * Fraction(1)
)
pairing_factor = norm_sq * Fraction(1, 3) * Fraction(1, 2) ** 2
gate_factor = Fraction(1, 8) * Fraction(1, 2) ** 2 * Fraction(1, 16)

assert three_branch_rank == 2
assert reduced_rank == 1
assert singlet == Fraction(1, 2)
assert norm_sq == Fraction(3, 4)
assert pairing_factor == Fraction(1, 16)
assert gate_factor == Fraction(1, 512)

certificate = {
    "calculations": {
        "gate_factor_from_coefficient_lowers_and_pairing": q(gate_factor),
        "pairing_factor_from_norm_and_dimensions": q(pairing_factor),
        "reduced_cycle_rank": reduced_rank,
        "singlet_projection_coefficient": q(singlet),
        "three_branch_cycle_rank": three_branch_rank,
        "witness_norm_sq_from_four_moments": q(norm_sq),
    },
    "domain": "0 < beta <= 1",
    "external_audit_verdict": None,
    "task": "(9) Fabricante del prisma theta",
}

print(json.dumps(certificate, indent=2, sort_keys=True, ensure_ascii=True))
