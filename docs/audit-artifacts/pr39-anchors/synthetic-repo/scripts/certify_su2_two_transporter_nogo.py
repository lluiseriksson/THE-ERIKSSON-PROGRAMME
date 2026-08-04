#!/usr/bin/env python3
"""Exact finite certificate for the SU(2) two-transporter no-go note.

This script checks only finite noncommutative word identities and one exact
unit-quaternion witness.  It is deliberately not a certificate for any Haar
integral identity.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import NoReturn


EXPECTED_CHECKS = 14
MUTATIONS = ("decisive-trace", "witness-condition", "omit-check")


class CertificateFailure(Exception):
    """A failed or structurally incomplete finite certificate."""


@dataclass
class CheckLedger:
    count: int = 0

    def require(self, condition: bool, label: str) -> None:
        """Record one acceptance check and fail explicitly if it is false."""
        self.count += 1
        if not condition:
            raise CertificateFailure(f"check {self.count} failed: {label}")

    def close(self) -> None:
        """Reject additions or removals that do not update the fixed contract."""
        if self.count != EXPECTED_CHECKS:
            raise CertificateFailure(
                f"check-count mismatch: observed {self.count}, expected {EXPECTED_CHECKS}"
            )


def fail(message: str) -> NoReturn:
    print(f"CERTIFICATE ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


@dataclass(frozen=True)
class Qsqrt2:
    """An exact element a + b*sqrt(2), with a,b in Q."""

    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    def __add__(self, other: object) -> "Qsqrt2":
        rhs = coerce(other)
        return Qsqrt2(self.a + rhs.a, self.b + rhs.b)

    __radd__ = __add__

    def __neg__(self) -> "Qsqrt2":
        return Qsqrt2(-self.a, -self.b)

    def __sub__(self, other: object) -> "Qsqrt2":
        return self + (-coerce(other))

    def __rsub__(self, other: object) -> "Qsqrt2":
        return coerce(other) - self

    def __mul__(self, other: object) -> "Qsqrt2":
        rhs = coerce(other)
        return Qsqrt2(
            self.a * rhs.a + 2 * self.b * rhs.b,
            self.a * rhs.b + self.b * rhs.a,
        )

    __rmul__ = __mul__

    def __str__(self) -> str:
        if self.b == 0:
            return str(self.a)
        if self.a == 0:
            return f"{self.b}*sqrt(2)"
        sign = "+" if self.b > 0 else "-"
        return f"{self.a}{sign}{abs(self.b)}*sqrt(2)"


def coerce(value: object) -> Qsqrt2:
    if isinstance(value, Qsqrt2):
        return value
    if isinstance(value, (int, Fraction)):
        return Qsqrt2(Fraction(value), Fraction(0))
    raise TypeError(f"cannot coerce {type(value)!r} to Qsqrt2")


ZERO = Qsqrt2()
ONE = Qsqrt2(Fraction(1))
SQRT2_OVER_2 = Qsqrt2(Fraction(0), Fraction(1, 2))


@dataclass(frozen=True)
class Quaternion:
    r: Qsqrt2 = ZERO
    i: Qsqrt2 = ZERO
    j: Qsqrt2 = ZERO
    k: Qsqrt2 = ZERO

    def __neg__(self) -> "Quaternion":
        return Quaternion(-self.r, -self.i, -self.j, -self.k)

    def __mul__(self, rhs: "Quaternion") -> "Quaternion":
        a, b, c, d = self.r, self.i, self.j, self.k
        e, f, g, h = rhs.r, rhs.i, rhs.j, rhs.k
        return Quaternion(
            a * e - b * f - c * g - d * h,
            a * f + b * e + c * h - d * g,
            a * g - b * h + c * e + d * f,
            a * h + b * g - c * f + d * e,
        )

    def conj(self) -> "Quaternion":
        return Quaternion(self.r, -self.i, -self.j, -self.k)

    def norm_sq(self) -> Qsqrt2:
        return self.r * self.r + self.i * self.i + self.j * self.j + self.k * self.k

    def trace(self) -> Qsqrt2:
        # Under the standard unit-quaternion isomorphism with SU(2), tr(q)=2 Re(q).
        return 2 * self.r

    def __str__(self) -> str:
        return f"({self.r}; {self.i}i; {self.j}j; {self.k}k)"


Q_ONE = Quaternion(r=ONE)
Q_I = Quaternion(i=ONE)
Q_J = Quaternion(j=ONE)
Q_K = Quaternion(k=ONE)


@dataclass(frozen=True)
class Letter:
    name: str
    sign: int = 1

    def inv(self) -> "Letter":
        return Letter(self.name, -self.sign)

    def __str__(self) -> str:
        return self.name if self.sign == 1 else f"{self.name}^-1"


@dataclass(frozen=True)
class Word:
    letters: tuple[Letter, ...] = ()

    @staticmethod
    def generator(name: str) -> "Word":
        return Word((Letter(name),))

    def __mul__(self, rhs: "Word") -> "Word":
        stack: list[Letter] = list(self.letters)
        for letter in rhs.letters:
            if stack and stack[-1] == letter.inv():
                stack.pop()
            else:
                stack.append(letter)
        return Word(tuple(stack))

    def inv(self) -> "Word":
        return Word(tuple(letter.inv() for letter in reversed(self.letters)))

    def __str__(self) -> str:
        return "1" if not self.letters else " ".join(map(str, self.letters))


def finite_word_checks(checks: CheckLedger, mutation: str | None) -> list[str]:
    x, y = Word.generator("x"), Word.generator("y")
    c, c1, c2 = Word.generator("c"), Word.generator("c1"), Word.generator("c2")
    z = Word.generator("z")
    reduced = x * y.inv()
    hd_diagonal = x * c * y.inv() * c.inv()
    he_diagonal = x * c * c.inv() * y.inv()
    hd = x * c1 * y.inv() * c2.inv()
    he = x * c1 * c2.inv() * y.inv()
    u = x * c1
    v_left = y * c2
    v_right = c2 * y
    a = x * c1 * y.inv()

    checks.require(hd_diagonal != reduced, "H_D diagonal must differ from reduced")
    checks.require(he_diagonal == reduced, "H_E diagonal must equal reduced")
    checks.require(he == u * v_left.inv(), "H_E must factor as u v_left^-1")
    checks.require(hd == u * v_right.inv(), "H_D must factor as u v_right^-1")
    checks.require(
        a * (a * z).inv() == a * z.inv() * a.inv(),
        "D substitution must give A z^-1 A^-1",
    )
    if mutation != "omit-check":
        checks.require(
            u * (u * z).inv() == u * z.inv() * u.inv(),
            "E substitution must give u z^-1 u^-1",
        )

    return [
        f"WORD H_D diagonal = {hd_diagonal} != {reduced}",
        f"WORD H_E diagonal = {he_diagonal} = reduced",
        f"WORD H_E = (x c1)(y c2)^-1 = {u * v_left.inv()}",
        f"WORD H_D = (x c1)(c2 y)^-1 = {u * v_right.inv()}",
        f"WORD D substitution c2=A z gives A z^-1 A^-1 = {a * (a * z).inv()}",
        f"WORD E substitution v=u z gives u z^-1 u^-1 = {u * (u * z).inv()}",
    ]


def quaternion_checks(checks: CheckLedger, mutation: str | None) -> list[str]:
    x, y = Q_I, Q_J
    c = Quaternion(r=SQRT2_OVER_2, k=SQRT2_OVER_2)
    checks.require(x.norm_sq() == ONE, "x witness must be a unit quaternion")
    checks.require(y.norm_sq() == ONE, "y witness must be a unit quaternion")
    expected_c_norm = Qsqrt2(Fraction(2)) if mutation == "witness-condition" else ONE
    checks.require(
        c.norm_sq() == expected_c_norm,
        "c witness must satisfy the exact unit-norm condition",
    )

    # The three factors used through conjugation have just been checked unit,
    # so quaternion conjugation is their inverse.
    reduced = x * y.conj()
    hd_diagonal = x * c * y.conj() * c.conj()
    he_diagonal = x * c * c.conj() * y.conj()

    checks.require(reduced == -Q_K, "reduced witness must equal -k")
    checks.require(hd_diagonal == -Q_ONE, "H_D witness must equal -1")
    checks.require(he_diagonal == reduced, "H_E witness must equal reduced")
    checks.require(reduced.trace() == ZERO, "reduced trace must be zero")
    expected_hd_trace = (
        Qsqrt2(Fraction(-1))
        if mutation == "decisive-trace"
        else Qsqrt2(Fraction(-2))
    )
    checks.require(
        mutation is None or hd_diagonal.trace() == expected_hd_trace,
        "H_D diagonal trace must be exactly -2",
    )

    return [
        f"QUAT c norm^2 = {c.norm_sq()}",
        f"QUAT reduced x y^-1 = {reduced}; trace = {reduced.trace()}",
        f"QUAT H_D(x,c,y,c) = {hd_diagonal}; trace = {hd_diagonal.trace()}",
        f"QUAT H_E(x,c,y,c) = {he_diagonal}; trace = {he_diagonal.trace()}",
        "WEIGHT reduced = exp((beta/2)*0) = 1",
        "WEIGHT H_D diagonal = exp((beta/2)*(-2)) = exp(-beta)",
    ]


def optimization_flags() -> list[str]:
    if sys.flags.optimize <= 0:
        return []
    return ["-" + "O" * sys.flags.optimize]


def self_test() -> int:
    script = str(Path(__file__).resolve())
    for mutation in MUTATIONS:
        command = [sys.executable, *optimization_flags(), script, "--_mutation", mutation]
        completed = subprocess.run(command, text=True, capture_output=True, check=False)
        combined = completed.stdout + completed.stderr
        if completed.returncode == 0:
            fail(f"self-test mutation {mutation!r} was accepted")
        if "RESULT: PASS" in combined:
            fail(f"self-test mutation {mutation!r} emitted RESULT: PASS")
        print(f"SELF-TEST mutation {mutation}: REJECTED (exit {completed.returncode})")
    print(f"SELF-TEST: PASS ({len(MUTATIONS)}/{len(MUTATIONS)} mutations rejected)")
    return 0


def certify(mutation: str | None = None) -> int:
    checks = CheckLedger()
    try:
        word_lines = finite_word_checks(checks, mutation)
        quaternion_lines = quaternion_checks(checks, mutation)
        checks.close()
    except (CertificateFailure, ArithmeticError, TypeError, ValueError) as exc:
        fail(str(exc))

    lines = [
        "SU2 TWO-TRANSPORTER FINITE ARITHMETIC/WITNESS CERTIFICATE",
        "scope: exact words + Q(sqrt(2)) unit quaternions; NOT Haar integration",
        *word_lines,
        *quaternion_lines,
        f"CHECKS: {checks.count}/{EXPECTED_CHECKS}",
        "RESULT: PASS",
    ]
    print("\n".join(lines))
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Certify the finite arithmetic/witness portion of the SU(2) no-go note."
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="verify that the built-in known mutations are all rejected",
    )
    parser.add_argument("--_mutation", choices=MUTATIONS, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.self_test and args._mutation is not None:
        parser.error("--self-test and --_mutation are mutually exclusive")
    return args


def main() -> int:
    args = parse_args()
    if args.self_test:
        return self_test()
    return certify(args._mutation)


if __name__ == "__main__":
    raise SystemExit(main())
