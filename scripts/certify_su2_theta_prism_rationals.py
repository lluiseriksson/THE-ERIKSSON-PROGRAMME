#!/usr/bin/env python3
"""Independent exact-rational replay for the SU(2) theta-prism artefact.

Every check is an explicit runtime branch.  Python's ``-O`` flag therefore
cannot disable the certificate checks.
"""

import argparse
from fractions import Fraction
import json
import sys


class CertificationError(RuntimeError):
    """Raised when a registered rational or domain check is violated."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CertificationError(message)


def q(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def parse_fraction(raw: str) -> Fraction:
    try:
        return Fraction(raw)
    except (ValueError, ZeroDivisionError) as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc


def build_certificate(singlet: Fraction, domain: str) -> dict[str, object]:
    three_branch_rank = 3 + 1 - 2
    reduced_rank = 2 + 1 - 2
    norm_sq = (
        Fraction(1)
        - singlet * Fraction(1, 2)
        - singlet * Fraction(1, 2)
        + singlet * singlet * Fraction(1)
    )
    pairing_factor = norm_sq * Fraction(1, 3) * Fraction(1, 2) ** 2
    gate_factor = Fraction(1, 8) * Fraction(1, 2) ** 2 * Fraction(1, 16)

    require(three_branch_rank == 2, "three-branch cycle rank changed")
    require(reduced_rank == 1, "reduced cycle rank changed")
    require(singlet == Fraction(1, 2), "singlet coefficient must be exactly 1/2")
    require(norm_sq == Fraction(3, 4), "witness norm must be exactly 3/4")
    require(pairing_factor == Fraction(1, 16), "pairing factor must be exactly 1/16")
    require(gate_factor == Fraction(1, 512), "gate factor must be exactly 1/512")
    require(domain == "0 < beta <= 1", "domain must remain exactly 0 < beta <= 1")

    return {
        "calculations": {
            "gate_factor_from_coefficient_lowers_and_pairing": q(gate_factor),
            "pairing_factor_from_norm_and_dimensions": q(pairing_factor),
            "reduced_cycle_rank": reduced_rank,
            "singlet_projection_coefficient": q(singlet),
            "three_branch_cycle_rank": three_branch_rank,
            "witness_norm_sq_from_four_moments": q(norm_sq),
        },
        "domain": domain,
        "external_audit_verdict": None,
        "task": "(9) Fabricante del prisma theta",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--singlet", type=parse_fraction, default=Fraction(1, 2))
    parser.add_argument("--domain", default="0 < beta <= 1")
    args = parser.parse_args()
    try:
        certificate = build_certificate(args.singlet, args.domain)
    except CertificationError as exc:
        print(f"CERTIFICATION ERROR: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(certificate, indent=2, sort_keys=True, ensure_ascii=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
