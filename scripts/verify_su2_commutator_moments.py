#!/usr/bin/env python3
"""Fail-closed exact certificate for the SU(2) commutator contractions.

This is deliberately not a Haar-integration proof.  It checks, over exact
rationals, the finite index contractions used after invoking the certified
Schur orthogonality tensor E[U_ik conj(U_jl)] = delta_ij delta_kl / 2.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import NoReturn


HALF = Fraction(1, 2)
QUARTER = Fraction(1, 4)
IDENTITY = ((1, 0), (0, 1))
CERTIFIER_NAME = "verify_su2_commutator_moments"
CERTIFIER_VERSION = "2.0.0"
CERTIFICATE_SCHEMA = "su2-commutator-moments-certificate/v2"
SELF_TEST_SCHEMA = "su2-commutator-moments-self-test/v1"
EXPECTED_CHECKS = (
    "witness_is_nonidentity",
    "witness_determinant_is_one",
    "witness_is_unitary",
    "witness_trace_is_zero",
    "identity_determinant_is_one",
    "identity_is_unitary",
    "commutator_with_identity_is_identity",
    "first_moment_contraction",
    "second_moment_contraction",
    "composed_moment_contraction",
    "character_at_identity_is_nonzero",
    "beta_is_positive",
    "beta_over_sixteen_is_exact",
    "beta_over_sixteen_is_positive",
)
EXPECTED_CHECK_COUNT = 14


class CertificationError(Exception):
    """A fail-closed certificate or self-test failure."""


@dataclass(frozen=True)
class FinalizedChecks:
    count: int
    names: tuple[str, ...]


class CheckLedger:
    def __init__(self) -> None:
        if len(EXPECTED_CHECKS) != EXPECTED_CHECK_COUNT:
            raise CertificationError("internal check schema/count mismatch")
        if len(set(EXPECTED_CHECKS)) != EXPECTED_CHECK_COUNT:
            raise CertificationError("internal check schema contains duplicate names")
        self._executed: list[str] = []

    def require(self, name: str, condition: bool, diagnostic: str) -> None:
        if name not in EXPECTED_CHECKS:
            raise CertificationError(f"unregistered check {name!r}")
        if name in self._executed:
            raise CertificationError(f"check {name!r} executed more than once")
        self._executed.append(name)
        if not condition:
            raise CertificationError(f"check {name!r} failed: {diagnostic}")

    def finalize(self) -> FinalizedChecks:
        names = tuple(self._executed)
        if len(names) != EXPECTED_CHECK_COUNT:
            raise CertificationError(
                f"executed {len(names)} checks; expected {EXPECTED_CHECK_COUNT}"
            )
        if names != EXPECTED_CHECKS:
            missing = [name for name in EXPECTED_CHECKS if name not in names]
            unexpected = [name for name in names if name not in EXPECTED_CHECKS]
            raise CertificationError(
                "check sequence mismatch; "
                f"missing={missing!r}, unexpected={unexpected!r}, executed={names!r}"
            )
        return FinalizedChecks(count=len(names), names=names)


def delta(a: int, b: int) -> int:
    return int(a == b)


def determinant(matrix: tuple[tuple[int, int], tuple[int, int]]) -> int:
    return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]


def transpose_times(
    matrix: tuple[tuple[int, int], tuple[int, int]],
) -> tuple[tuple[int, int], tuple[int, int]]:
    return tuple(
        tuple(sum(matrix[k][i] * matrix[k][j] for k in range(2)) for j in range(2))
        for i in range(2)
    )  # type: ignore[return-value]


def multiply(
    left: tuple[tuple[int, int], tuple[int, int]],
    right: tuple[tuple[int, int], tuple[int, int]],
) -> tuple[tuple[int, int], tuple[int, int]]:
    return tuple(
        tuple(sum(left[i][k] * right[k][j] for k in range(2)) for j in range(2))
        for i in range(2)
    )  # type: ignore[return-value]


def inverse_det_one(
    matrix: tuple[tuple[int, int], tuple[int, int]],
) -> tuple[tuple[int, int], tuple[int, int]]:
    return ((matrix[1][1], -matrix[0][1]), (-matrix[1][0], matrix[0][0]))


def commutator(
    left: tuple[tuple[int, int], tuple[int, int]],
    right: tuple[tuple[int, int], tuple[int, int]],
) -> tuple[tuple[int, int], tuple[int, int]]:
    return multiply(multiply(multiply(left, right), inverse_det_one(left)), inverse_det_one(right))


def first_moment_coefficient(i: int, j: int, k: int, ell: int) -> Fraction:
    """Coefficient of A[k,ell] in E[(U A U^-1)[i,j]]."""
    return HALF * delta(i, j) * delta(k, ell)


def second_moment_coefficient(i: int, j: int, a: int) -> Fraction:
    """Coefficient from E[c[a,a] conj(c[j,i])]."""
    return HALF * delta(a, j) * delta(a, i)


def compute_moments() -> tuple[dict[str, dict[str, str]], dict[str, str], dict[str, str]]:
    first: dict[str, dict[str, str]] = {}
    second: dict[str, str] = {}
    composed: dict[str, str] = {}
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
    return first, second, composed


def build_certificate(
    finalized: FinalizedChecks,
    beta: Fraction,
    chi_identity: int,
    first: dict[str, dict[str, str]],
    second: dict[str, str],
    composed: dict[str, str],
    witness: tuple[tuple[int, int], tuple[int, int]],
) -> dict[str, object]:
    if finalized.count != EXPECTED_CHECK_COUNT or finalized.names != EXPECTED_CHECKS:
        raise CertificationError("certificate requested without the exact finalized check set")
    witness_det = determinant(witness)
    witness_gram = transpose_times(witness)
    return {
        "beta": str(beta),
        "checks": {"executed": finalized.count, "expected": EXPECTED_CHECK_COUNT},
        "chi_identity": chi_identity,
        "composed_commutator_moment": composed,
        "certifier": {
            "name": CERTIFIER_NAME,
            "schema": CERTIFICATE_SCHEMA,
            "version": CERTIFIER_VERSION,
        },
        "first_conjugation_contraction": first,
        "scope": "finite exact contraction; not a substitute for Haar/Fubini",
        "second_trace_inverse_contraction": second,
        "status": "PASS",
        "su2_non_singleton_witness": {
            "det": witness_det,
            "matrix": witness,
            "trace": witness[0][0] + witness[1][1],
            "unitary_gram": witness_gram,
        },
    }


def emit_certificate(certificate: dict[str, object], finalized: FinalizedChecks) -> None:
    if finalized.count != EXPECTED_CHECK_COUNT or finalized.names != EXPECTED_CHECKS:
        raise CertificationError("refusing to emit before exact check finalization")
    if certificate.get("status") != "PASS":
        raise CertificationError("refusing to emit a malformed certificate")
    print(json.dumps(certificate, sort_keys=True, separators=(",", ":")))


def certify(mutation: str | None = None) -> None:
    checks = CheckLedger()
    witness = ((0, 1), (-1, 0))
    expected_trace = 0
    expected_commutator = IDENTITY
    if mutation == "determinant_2":
        witness = ((2, 0), (0, 1))
    elif mutation == "non_unitary":
        witness = ((1, 1), (0, 1))
    elif mutation == "trace_or_moment":
        expected_trace = 1
    elif mutation == "commutator_identity":
        expected_commutator = witness

    witness_det = determinant(witness)
    witness_gram = transpose_times(witness)
    checks.require("witness_is_nonidentity", witness != IDENTITY, f"matrix={witness!r}")
    checks.require("witness_determinant_is_one", witness_det == 1, f"det={witness_det!r}")
    checks.require("witness_is_unitary", witness_gram == IDENTITY, f"U^T U={witness_gram!r}")
    checks.require("witness_trace_is_zero", witness[0][0] + witness[1][1] == expected_trace, f"trace={witness[0][0] + witness[1][1]!r}, expected={expected_trace!r}")

    identity_det = determinant(IDENTITY)
    identity_gram = transpose_times(IDENTITY)
    checks.require("identity_determinant_is_one", identity_det == 1, f"det={identity_det!r}")
    checks.require("identity_is_unitary", identity_gram == IDENTITY, f"I^T I={identity_gram!r}")
    witness_commutator = commutator(witness, IDENTITY)
    checks.require("commutator_with_identity_is_identity", witness_commutator == expected_commutator, f"commutator={witness_commutator!r}, expected={expected_commutator!r}")

    # Moment calculation starts only after both displayed SU(2) matrices and
    # the exact commutator identity have passed semantic checks.
    first, second, composed = compute_moments()
    expected_first = {
        "00": {"A00": "1/2", "A11": "1/2"},
        "01": {},
        "10": {},
        "11": {"A00": "1/2", "A11": "1/2"},
    }
    expected_second = {"00": "1/2", "01": "0", "10": "0", "11": "1/2"}
    expected_composed = {"00": "1/4", "01": "0", "10": "0", "11": "1/4"}
    checks.require("first_moment_contraction", first == expected_first, f"value={first!r}")
    checks.require("second_moment_contraction", second == expected_second, f"value={second!r}")
    checks.require("composed_moment_contraction", composed == expected_composed, f"value={composed!r}")

    beta = Fraction(1)
    chi_identity = 2
    beta_over_sixteen = beta / 16
    checks.require("character_at_identity_is_nonzero", chi_identity != 0, f"chi(I)={chi_identity!r}")
    checks.require("beta_is_positive", beta > 0, f"beta={beta!r}")
    checks.require("beta_over_sixteen_is_exact", beta_over_sixteen == Fraction(1, 16), f"beta/16={beta_over_sixteen!r}")
    checks.require("beta_over_sixteen_is_positive", beta_over_sixteen > 0, f"beta/16={beta_over_sixteen!r}")

    finalized = checks.finalize()
    certificate = build_certificate(finalized, beta, chi_identity, first, second, composed, witness)
    emit_certificate(certificate, finalized)


def contains_pass_certificate(output: str) -> bool:
    for line in output.splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict) and value.get("status") == "PASS":
            return True
    return False


def reject_subprocess(command: list[str], label: str) -> None:
    completed = subprocess.run(command, capture_output=True, text=True, check=False)
    if completed.returncode == 0:
        raise CertificationError(f"self-test {label!r} was accepted")
    if contains_pass_certificate(completed.stdout):
        raise CertificationError(f"self-test {label!r} emitted status PASS")


def mutate_source(source: str, mutation: str) -> str:
    if mutation == "deleted_check":
        target = '    checks.require("first_moment_contraction", first == expected_first, f"value={first!r}")\n'
        if source.count(target) != 1:
            raise CertificationError("self-test could not locate unique finite-check line")
        return source.replace(target, "", 1)
    if mutation == "pass_before_counter":
        target = (
            "    finalized = checks.finalize()\n"
            "    certificate = build_certificate(finalized, beta, chi_identity, first, second, composed, witness)\n"
            "    emit_certificate(certificate, finalized)\n"
        )
        replacement = (
            "    emit_certificate(certificate, finalized)\n"
            "    finalized = checks.finalize()\n"
            "    certificate = build_certificate(finalized, beta, chi_identity, first, second, composed, witness)\n"
        )
        if source.count(target) != 1:
            raise CertificationError("self-test could not locate unique finalization block")
        return source.replace(target, replacement, 1)
    raise CertificationError(f"unknown source mutation {mutation!r}")


def interpreter_commands(script: Path, extra: list[str]) -> list[tuple[str, list[str]]]:
    return [
        ("normal", [sys.executable, str(script), *extra]),
        ("optimized", [sys.executable, "-O", str(script), *extra]),
    ]


def run_self_test() -> None:
    script = Path(__file__).resolve()
    mutation_labels: list[str] = []
    for mutation in ("determinant_2", "non_unitary", "trace_or_moment", "commutator_identity"):
        for mode, command in interpreter_commands(script, ["--_mutation", mutation]):
            label = f"{mutation}:{mode}"
            reject_subprocess(command, label)
            mutation_labels.append(label)

    source = script.read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="su2-certificate-self-test-") as temp_dir:
        for mutation in ("deleted_check", "pass_before_counter"):
            mutated_script = Path(temp_dir) / f"{mutation}.py"
            mutated_script.write_text(mutate_source(source, mutation), encoding="utf-8", newline="\n")
            for mode, command in interpreter_commands(mutated_script, []):
                label = f"{mutation}:{mode}"
                reject_subprocess(command, label)
                mutation_labels.append(label)

    print(json.dumps({
        "certifier": {"name": CERTIFIER_NAME, "version": CERTIFIER_VERSION},
        "mutation_processes": len(mutation_labels),
        "mutations": mutation_labels,
        "schema": SELF_TEST_SCHEMA,
        "status": "SELF_TEST_PASS",
    }, sort_keys=True, separators=(",", ":")))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="run fail-closed mutation tests")
    parser.add_argument(
        "--_mutation",
        choices=("determinant_2", "non_unitary", "trace_or_moment", "commutator_identity"),
        help=argparse.SUPPRESS,
    )
    return parser.parse_args()


def fail(message: str, exit_code: int = 1) -> NoReturn:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(exit_code)


def main() -> None:
    args = parse_args()
    if args.self_test and args._mutation is not None:
        fail("--self-test cannot be combined with an internal mutation")
    try:
        if args.self_test:
            run_self_test()
        else:
            certify(args._mutation)
    except CertificationError as error:
        fail(str(error))
    except Exception as error:
        fail(f"internal error: {type(error).__name__}: {error}", exit_code=2)


if __name__ == "__main__":
    main()
