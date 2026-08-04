"""Exact rational partition shared by the finite scaled production lanes."""

from fractions import Fraction


BETA_START = Fraction(20)
BETA_STOP = Fraction(1000, 9)
BETA_STEP = Fraction(1, 10)


def fraction_string(value: Fraction) -> str:
    return (str(value.numerator) if value.denominator == 1
            else f"{value.numerator}/{value.denominator}")


def beta_intervals():
    rows = []
    cursor = BETA_START
    while cursor < BETA_STOP:
        upper = min(cursor+BETA_STEP, BETA_STOP)
        rows.append((cursor, upper))
        cursor = upper
    return tuple(rows)


BETA_INTERVALS = beta_intervals()
UNIT_SIZE = 10
UNITS = tuple(
    (start, min(start+UNIT_SIZE, len(BETA_INTERVALS)))
    for start in range(0, len(BETA_INTERVALS), UNIT_SIZE)
)


def unit_slug(unit) -> str:
    return f"beta_{unit[0]:04d}_{unit[1]:04d}"


def unit_map():
    return {unit_slug(unit): unit for unit in UNITS}
