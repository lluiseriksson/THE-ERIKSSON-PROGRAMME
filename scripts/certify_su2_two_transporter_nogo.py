#!/usr/bin/env python3
"""Exact finite certificate for the SU(2) two-transporter no-go note.

This script checks only finite noncommutative word identities and one exact
unit-quaternion witness.  It is deliberately not a certificate for any Haar
integral identity.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


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

    def inv_unit(self) -> "Quaternion":
        assert self.norm_sq() == ONE
        return self.conj()

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


def finite_word_checks() -> list[str]:
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

    assert hd_diagonal != reduced
    assert he_diagonal == reduced
    assert he == u * v_left.inv()
    assert hd == u * v_right.inv()
    assert a * (a * z).inv() == a * z.inv() * a.inv()
    assert u * (u * z).inv() == u * z.inv() * u.inv()

    return [
        f"WORD H_D diagonal = {hd_diagonal} != {reduced}",
        f"WORD H_E diagonal = {he_diagonal} = reduced",
        f"WORD H_E = (x c1)(y c2)^-1 = {u * v_left.inv()}",
        f"WORD H_D = (x c1)(c2 y)^-1 = {u * v_right.inv()}",
        f"WORD D substitution c2=A z gives A z^-1 A^-1 = {a * (a * z).inv()}",
        f"WORD E substitution v=u z gives u z^-1 u^-1 = {u * (u * z).inv()}",
    ]


def quaternion_checks() -> list[str]:
    x, y = Q_I, Q_J
    c = Quaternion(r=SQRT2_OVER_2, k=SQRT2_OVER_2)
    assert all(q.norm_sq() == ONE for q in (x, y, c))

    reduced = x * y.inv_unit()
    hd_diagonal = x * c * y.inv_unit() * c.inv_unit()
    he_diagonal = x * c * c.inv_unit() * y.inv_unit()

    assert reduced == -Q_K
    assert hd_diagonal == -Q_ONE
    assert he_diagonal == reduced
    assert reduced.trace() == ZERO
    assert hd_diagonal.trace() == Qsqrt2(Fraction(-2))

    return [
        f"QUAT c norm^2 = {c.norm_sq()}",
        f"QUAT reduced x y^-1 = {reduced}; trace = {reduced.trace()}",
        f"QUAT H_D(x,c,y,c) = {hd_diagonal}; trace = {hd_diagonal.trace()}",
        f"QUAT H_E(x,c,y,c) = {he_diagonal}; trace = {he_diagonal.trace()}",
        "WEIGHT reduced = exp((beta/2)*0) = 1",
        "WEIGHT H_D diagonal = exp((beta/2)*(-2)) = exp(-beta)",
    ]


def main() -> int:
    lines = [
        "SU2 TWO-TRANSPORTER FINITE CERTIFICATE",
        "scope: exact words + Q(sqrt(2)) unit quaternions; NOT Haar integration",
        *finite_word_checks(),
        *quaternion_checks(),
        "RESULT: PASS",
    ]
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
