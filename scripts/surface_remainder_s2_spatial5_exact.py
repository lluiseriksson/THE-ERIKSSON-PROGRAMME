"""Exact delta-second jets with a degree-five spatial Taylor enclosure.

This module is an isolated successor for the literal S2''' judge.  It keeps
the exact scaled-Bessel recurrences, carries a normalized delta jet through
order two, integrates spatial Taylor degrees zero through four exactly, and
charges only the total-degree-five spatial remainder.

It is certificate infrastructure only until a frozen positive delta
partition, its analytic delta=0 patch, production/replay transcripts, and the
literal weighted sum all pass.
"""

from __future__ import annotations

from dataclasses import dataclass
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from math import factorial

from flint import arb, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_positive_physical_spatial3 import linear_moment
from surface_remainder_spatial_jet3 import (
    INDICES,
    Jet3,
    jadd,
    jcos,
    jexp,
    jinv,
    jmul,
    jneg,
    jscale,
    jsin,
    jsqrt,
    jet,
    variable_x,
    variable_y,
)
from surface_remainder_tjet import TJet, tjet


def _arb(value: object) -> arb:
    return value if isinstance(value, arb) else arb(str(value))


@dataclass(frozen=True)
class DeltaJet2:
    """Normalized Taylor jet ``c0 + c1*h + c2*h^2`` in delta."""

    c0: arb
    c1: arb = arb(0)
    c2: arb = arb(0)
    _jet_scalar_marker = True

    def __add__(self, other: object) -> "DeltaJet2":
        other = djet(other)
        return DeltaJet2(
            self.c0 + other.c0, self.c1 + other.c1, self.c2 + other.c2
        )

    __radd__ = __add__

    def __neg__(self) -> "DeltaJet2":
        return DeltaJet2(-self.c0, -self.c1, -self.c2)

    def __sub__(self, other: object) -> "DeltaJet2":
        return self + (-djet(other))

    def __rsub__(self, other: object) -> "DeltaJet2":
        return djet(other) - self

    def __mul__(self, other: object) -> "DeltaJet2":
        other = djet(other)
        return DeltaJet2(
            self.c0 * other.c0,
            self.c0 * other.c1 + self.c1 * other.c0,
            self.c0 * other.c2 + self.c1 * other.c1 + self.c2 * other.c0,
        )

    __rmul__ = __mul__

    def inv(self) -> "DeltaJet2":
        return DeltaJet2(
            1 / self.c0,
            -self.c1 / self.c0**2,
            self.c1**2 / self.c0**3 - self.c2 / self.c0**2,
        )

    def __truediv__(self, other: object) -> "DeltaJet2":
        return self * djet(other).inv()

    def __rtruediv__(self, other: object) -> "DeltaJet2":
        return djet(other) * self.inv()

    def __pow__(self, power: int) -> "DeltaJet2":
        if not isinstance(power, int):
            raise TypeError("DeltaJet2 only supports integer powers")
        if power < 0:
            return (self.inv()) ** (-power)
        out, base, exponent = djet(1), self, power
        while exponent:
            if exponent & 1:
                out *= base
            exponent >>= 1
            if exponent:
                base *= base
        return out

    def compose(self, value: arb, first: arb, second: arb) -> "DeltaJet2":
        """Compose using ordinary outer derivatives."""

        return DeltaJet2(
            value,
            first * self.c1,
            first * self.c2 + second * self.c1**2 / 2,
        )

    def sqrt(self) -> "DeltaJet2":
        root = self.c0.sqrt()
        return self.compose(root, 1 / (2 * root), -1 / (4 * root**3))

    def exp(self) -> "DeltaJet2":
        value = self.c0.exp()
        return self.compose(value, value, value)

    def sin(self) -> "DeltaJet2":
        return self.compose(self.c0.sin(), self.c0.cos(), -self.c0.sin())

    def cos(self) -> "DeltaJet2":
        return self.compose(self.c0.cos(), -self.c0.sin(), -self.c0.cos())

    def is_finite(self) -> bool:
        return self.c0.is_finite() and self.c1.is_finite() and self.c2.is_finite()


def djet(value: object, first: object = 0, second_half: object = 0) -> DeltaJet2:
    return (
        value
        if isinstance(value, DeltaJet2)
        else DeltaJet2(_arb(value), _arb(first), _arb(second_half))
    )


Laurent = dict[int, Fraction]


def _laurent_add(*terms: Laurent) -> Laurent:
    out: Laurent = {}
    for term in terms:
        for exponent, coefficient in term.items():
            out[exponent] = out.get(exponent, Fraction(0)) + coefficient
    return {exponent: value for exponent, value in out.items() if value}


def _laurent_scale(term: Laurent, value: Fraction) -> Laurent:
    return {exponent: value * coefficient for exponent, coefficient in term.items()}


def _laurent_shift(term: Laurent, shift: int) -> Laurent:
    return {exponent + shift: coefficient for exponent, coefficient in term.items()}


def _laurent_derivative(term: Laurent) -> Laurent:
    return {
        exponent - 1: coefficient * exponent
        for exponent, coefficient in term.items()
        if exponent
    }


def _advance_pair(p: Laurent, q: Laurent) -> tuple[Laurent, Laurent]:
    """Differentiate ``p(z) A(z) + q(z) C(z)`` exactly."""

    p_next = _laurent_add(
        _laurent_derivative(p),
        _laurent_scale(p, Fraction(-1)),
        _laurent_scale(_laurent_shift(p, -1), Fraction(-2)),
        _laurent_shift(q, 1),
    )
    q_next = _laurent_add(
        _laurent_derivative(q),
        _laurent_scale(q, Fraction(-1)),
        _laurent_shift(p, -1),
    )
    return p_next, q_next


def _coefficient_table(family: str, max_order: int) -> list[tuple[Laurent, Laurent]]:
    if family == "A":
        pair = ({0: Fraction(1)}, {})
    elif family == "B":
        # B=(C-2A)/z^2.
        pair = ({-2: Fraction(-2)}, {-2: Fraction(1)})
    else:
        raise ValueError(family)
    out = [pair]
    for _ in range(max_order):
        pair = _advance_pair(*pair)
        out.append(pair)
    return out


def _eval_laurent(term: Laurent, z: arb) -> arb:
    total = arb(0)
    for exponent, coefficient in term.items():
        scalar = arb(coefficient.numerator) / arb(coefficient.denominator)
        total += scalar * z**exponent
    return total


def _endpoint_derivatives(z: arb, family: str, max_order: int) -> list[arb]:
    a = (-z).exp() * z.bessel_i(1) / z
    c = (-z).exp() * z.bessel_i(0)
    return [
        _eval_laurent(p, z) * a + _eval_laurent(q, z) * c
        for p, q in _coefficient_table(family, max_order)
    ]


def scaled_bessel_derivatives(
    z: arb, family: str, max_order: int = 7
) -> list[arb]:
    """Enclose derivatives of A or B on ``z`` by complete monotonicity."""

    if z.lower() <= 4:
        raise ValueError("exact spatial-five lane requires z>4")
    zl, zh = arb(z.lower()), arb(z.upper())
    left = _endpoint_derivatives(zl, family, max_order)
    right = _endpoint_derivatives(zh, family, max_order)
    result = [
        hull(right[n], left[n]) if n % 2 == 0 else hull(left[n], right[n])
        for n in range(max_order + 1)
    ]
    for order, value in enumerate(result):
        if order % 2 == 0 and not value.lower() > 0:
            raise ValueError("even scaled-Bessel derivative lost positivity")
        if order % 2 == 1 and not value.upper() < 0:
            raise ValueError("odd scaled-Bessel derivative lost negativity")
    return result


def _spatial_compose(z: Jet3, family: str) -> Jet3:
    """Compose A/B with a spatial-five jet carrying delta-two scalars."""

    center = djet(z.get(0, 0))
    derivatives = scaled_bessel_derivatives(center.c0, family, 7)
    normalized = [
        center.compose(
            derivatives[order],
            derivatives[order + 1],
            derivatives[order + 2],
        )
        / factorial(order)
        for order in range(6)
    ]
    increment = Jet3(
        {
            index: (djet(0) if index == (0, 0) else z.get(*index))
            for index in INDICES
        }
    )
    powers = [jet(djet(1))]
    for _ in range(5):
        powers.append(jmul(powers[-1], increment))
    out = jet(djet(0))
    for coefficient, power in zip(normalized, powers):
        out = jadd(out, jscale(power, coefficient))
    return out


def _spatial_compose_tjet(z: Jet3, family: str) -> Jet3:
    """Spatial-five composition whose scalar coefficients carry delta-four."""

    center = z.get(0, 0)
    if not isinstance(center, TJet):
        raise TypeError("TJet spatial composition requires a TJet centre")
    derivatives = scaled_bessel_derivatives(center.v, family, 9)
    normalized = [
        center._compose(
            [
                derivatives[order + delta_order] / arb(factorial(delta_order))
                for delta_order in range(5)
            ]
        )
        / factorial(order)
        for order in range(6)
    ]
    increment = Jet3(
        {
            index: (tjet(0) if index == (0, 0) else z.get(*index))
            for index in INDICES
        }
    )
    powers = [jet(tjet(1))]
    for _ in range(5):
        powers.append(jmul(powers[-1], increment))
    out = jet(tjet(0))
    for coefficient, power in zip(normalized, powers):
        out = jadd(out, jscale(power, coefficient))
    return out


def _apply_radius_floor(radius2: Jet3) -> Jet3:
    """Intersect the constant value with the analytic physical-square floor."""

    u = arb("0.6").sin() ** 2
    floor = 2 * (1 - u) ** 2
    coefficients = dict(radius2.coefficients)
    value = djet(radius2.get(0, 0))
    band = hull(floor, arb(value.c0.upper()))
    coefficients[0, 0] = DeltaJet2(
        value.c0.intersection(band), value.c1, value.c2
    )
    return Jet3(coefficients)


def physical_moment_parts(
    delta_value: arb, t_value: arb, s: Jet3, alpha: Jet3
) -> tuple[dict[str, Jet3], Jet3]:
    """Exact physical-square moment prefactors and residual phase."""

    delta = djet(delta_value, 1, 0)
    beta = delta.inv()
    c, s4 = (t_value / 4).cos(), (t_value / 4).sin()
    p = jmul(jsin(jscale(s, arb(1) / 2)), jsin(jscale(s, arb(1) / 2)))
    q = jmul(
        jsin(jscale(alpha, arb(1) / 2)),
        jsin(jscale(alpha, arb(1) / 2)),
    )
    radius2 = jadd(
        jscale(jmul(jadd(1, jneg(p)), jadd(1, jneg(q))), 4 * c**2),
        jscale(jmul(p, q), 4 * s4**2),
    )
    radius = jsqrt(_apply_radius_floor(radius2))
    z = jscale(radius, 2 * beta)
    a_scaled = _spatial_compose(z, "A")
    b_scaled = _spatial_compose(z, "B")
    dweight = jscale(jadd(1, jneg(jadd(p, q))), 2)
    cc = 2 * c**2 - 1
    cos_s, cos_a = jcos(s), jcos(alpha)
    fluctuation = jmul(
        jadd(cos_s, -1),
        jadd(
            jscale(jadd(jscale(cos_s, 2), 1), cc),
            jmul(cos_a, jadd(cos_s, 1 + cc)),
        ),
    )
    beta_sqrt = beta.sqrt()
    kernel = jscale(a_scaled, 2 * beta**2 * beta_sqrt)
    hkernel = jscale(b_scaled, beta * beta_sqrt)
    # ``radius`` is independent of delta in fixed physical coordinates.
    # Forming ``2*beta*radius - 4*c*beta`` as two interval products destroys
    # their shared beta dependency on a delta box.  Factor beta first; this is
    # an exact ring identity and preserves the saddle cancellation before any
    # outward rounding.
    phase = jscale(jadd(jscale(radius, 2), -4 * c), beta)
    return {
        "KD": jmul(kernel, dweight),
        "KF": jmul(kernel, fluctuation),
        "HDD": jmul(hkernel, jmul(dweight, dweight)),
        "HDF": jmul(hkernel, jmul(dweight, fluctuation)),
    }, phase


def _apply_radius_floor_tjet(radius2: Jet3) -> Jet3:
    u = arb("0.6").sin() ** 2
    floor = 2 * (1 - u) ** 2
    coefficients = dict(radius2.coefficients)
    value = radius2.get(0, 0)
    if isinstance(value, TJet):
        band = hull(floor, arb(value.v.upper()))
        coefficients[0, 0] = TJet(
            value.v.intersection(band), value.d, value.d2, value.d3, value.d4
        )
    else:
        band = hull(floor, arb(value.upper()))
        coefficients[0, 0] = value.intersection(band)
    return Jet3(coefficients)


def physical_moment_parts_tjet(
    delta: TJet, t_value: arb, s: Jet3, alpha: Jet3
) -> tuple[dict[str, Jet3], Jet3]:
    """Exact physical moments with ordinary delta derivatives through four."""

    beta = 1 / delta
    c, s4 = (t_value / 4).cos(), (t_value / 4).sin()
    p = jmul(jsin(jscale(s, arb(1) / 2)), jsin(jscale(s, arb(1) / 2)))
    q = jmul(
        jsin(jscale(alpha, arb(1) / 2)),
        jsin(jscale(alpha, arb(1) / 2)),
    )
    radius2 = jadd(
        jscale(jmul(jadd(1, jneg(p)), jadd(1, jneg(q))), 4 * c**2),
        jscale(jmul(p, q), 4 * s4**2),
    )
    radius = jsqrt(_apply_radius_floor_tjet(radius2))
    z = jscale(radius, 2 * beta)
    a_scaled = _spatial_compose_tjet(z, "A")
    b_scaled = _spatial_compose_tjet(z, "B")
    dweight = jscale(jadd(1, jneg(jadd(p, q))), 2)
    cc = 2 * c**2 - 1
    cos_s, cos_a = jcos(s), jcos(alpha)
    fluctuation = jmul(
        jadd(cos_s, -1),
        jadd(
            jscale(jadd(jscale(cos_s, 2), 1), cc),
            jmul(cos_a, jadd(cos_s, 1 + cc)),
        ),
    )
    beta_sqrt = beta.sqrt()
    kernel = jscale(a_scaled, 2 * beta**2 * beta_sqrt)
    hkernel = jscale(b_scaled, beta * beta_sqrt)
    # Exact fixed-coordinate rationalization of the shared beta factor.
    phase = jscale(jadd(jscale(radius, 2), -4 * c), beta)
    return {
        "KD": jmul(kernel, dweight),
        "KF": jmul(kernel, fluctuation),
        "HDD": jmul(hkernel, jmul(dweight, dweight)),
        "HDF": jmul(hkernel, jmul(dweight, fluctuation)),
    }, phase


def calibration_jet(
    delta_value: arb,
    center: arb,
    coefficients: tuple[arb, arb, arb],
) -> DeltaJet2:
    """Exact quadratic gauge selected before a judging run."""

    shift = djet(delta_value - center, 1, 0)
    return djet(coefficients[0]) + coefficients[1] * shift + coefficients[2] * shift**2


def _calibrate(
    prefactors: dict[str, Jet3], calibration: DeltaJet2
) -> dict[str, Jet3]:
    out = dict(prefactors)
    out["KF"] = jadd(out["KF"], jneg(jscale(out["KD"], calibration)))
    out["HDF"] = jadd(out["HDF"], jneg(jscale(out["HDD"], calibration)))
    return out


def _remove_constant_and_linear(phase: Jet3, gx: arb, gy: arb) -> Jet3:
    coefficients = dict(phase.coefficients)
    coefficients[0, 0] = djet(0)
    coefficients[1, 0] = djet(phase.get(1, 0)) - gx
    coefficients[0, 1] = djet(phase.get(0, 1)) - gy
    return Jet3(coefficients)


def _remove_constant_and_linear_tjet(phase: Jet3, gx: arb, gy: arb) -> Jet3:
    coefficients = dict(phase.coefficients)
    coefficients[0, 0] = tjet(0)
    coefficients[1, 0] = phase.get(1, 0) - gx
    coefficients[0, 1] = phase.get(0, 1) - gy
    return Jet3(coefficients)


def centered_cell(
    delta: arb,
    t: arb,
    slo: arb,
    shi: arb,
    alo: arb,
    ahi: arb,
    calibration: DeltaJet2,
) -> dict[str, DeltaJet2]:
    """Degree-four exact integral plus degree-five spatial remainder."""

    sm, am = (slo + shi) / 2, (alo + ahi) / 2
    rx, ry = (shi - slo) / 2, (ahi - alo) / 2
    center_pref, center_phase = physical_moment_parts(
        delta, t, variable_x(sm), variable_y(am)
    )
    box_pref, box_phase = physical_moment_parts(
        delta,
        t,
        variable_x(hull(slo, shi)),
        variable_y(hull(alo, ahi)),
    )
    center_pref = _calibrate(center_pref, calibration)
    box_pref = _calibrate(box_pref, calibration)

    phase_center = djet(center_phase.get(0, 0))
    gx = arb(djet(center_phase.get(1, 0)).c0.mid())
    gy = arb(djet(center_phase.get(0, 1)).c0.mid())
    center_residual = jexp(_remove_constant_and_linear(center_phase, gx, gy))
    box_residual = jexp(_remove_constant_and_linear(box_phase, gx, gy))
    mx = [linear_moment(gx, 2 * rx, order) for order in range(5)]
    my = [linear_moment(gy, 2 * ry, order) for order in range(5)]
    mass = mx[0] * my[0]
    out: dict[str, DeltaJet2] = {}
    for name in center_pref:
        center_value = jmul(center_pref[name], center_residual)
        box_value = jmul(box_pref[name], box_residual)
        retained = djet(0)
        for degree in range(5):
            for i in range(degree + 1):
                j = degree - i
                retained += djet(center_value.get(i, j)) * mx[i] * my[j]
        errors = [arb(0), arb(0), arb(0)]
        for i in range(6):
            for j in range(6 - i):
                if i + j != 5:
                    continue
                coefficient = djet(box_value.get(i, j))
                factor = rx**i * ry**j * mass
                for order, component in enumerate(
                    (coefficient.c0, coefficient.c1, coefficient.c2)
                ):
                    errors[order] += arb(component.abs_upper()) * factor
        remainder = DeltaJet2(
            errors[0] * arb("0 +/- 1"),
            errors[1] * arb("0 +/- 1"),
            errors[2] * arb("0 +/- 1"),
        )
        out[name] = 4 * phase_center.exp() * (retained + remainder)
    return out


def calibration_tjet(
    delta: TJet,
    center: arb,
    coefficients: tuple[arb, arb, arb],
) -> TJet:
    shift = delta - center
    return coefficients[0] + coefficients[1] * shift + coefficients[2] * shift**2


def _calibrate_tjet(
    prefactors: dict[str, Jet3], calibration: TJet
) -> dict[str, Jet3]:
    out = dict(prefactors)
    out["KF"] = jadd(out["KF"], jneg(jscale(out["KD"], calibration)))
    out["HDF"] = jadd(out["HDF"], jneg(jscale(out["HDD"], calibration)))
    return out


def centered_cell_tjet(
    delta: TJet,
    t: arb,
    slo: arb,
    shi: arb,
    alo: arb,
    ahi: arb,
    calibration: TJet,
) -> dict[str, TJet]:
    """Spatial-five enclosure of value and four delta derivatives."""

    sm, am = (slo + shi) / 2, (alo + ahi) / 2
    rx, ry = (shi - slo) / 2, (ahi - alo) / 2
    center_pref, center_phase = physical_moment_parts_tjet(
        delta, t, variable_x(sm), variable_y(am)
    )
    box_pref, box_phase = physical_moment_parts_tjet(
        delta,
        t,
        variable_x(hull(slo, shi)),
        variable_y(hull(alo, ahi)),
    )
    center_pref = _calibrate_tjet(center_pref, calibration)
    box_pref = _calibrate_tjet(box_pref, calibration)
    phase_center = center_phase.get(0, 0)
    gx = arb(center_phase.get(1, 0).v.mid())
    gy = arb(center_phase.get(0, 1).v.mid())
    center_residual = jexp(
        _remove_constant_and_linear_tjet(center_phase, gx, gy)
    )
    box_residual = jexp(_remove_constant_and_linear_tjet(box_phase, gx, gy))
    mx = [linear_moment(gx, 2 * rx, order) for order in range(5)]
    my = [linear_moment(gy, 2 * ry, order) for order in range(5)]
    mass = mx[0] * my[0]
    out: dict[str, TJet] = {}
    for name in center_pref:
        center_value = jmul(center_pref[name], center_residual)
        box_value = jmul(box_pref[name], box_residual)
        retained = tjet(0)
        for degree in range(5):
            for i in range(degree + 1):
                j = degree - i
                retained += center_value.get(i, j) * mx[i] * my[j]
        errors = [arb(0) for _ in range(5)]
        for i in range(6):
            for j in range(6 - i):
                if i + j != 5:
                    continue
                coefficient = box_value.get(i, j)
                factor = rx**i * ry**j * mass
                for order, component in enumerate(coefficient.derivatives()):
                    errors[order] += arb(component.abs_upper()) * factor
        remainder = TJet(
            *(error * arb("0 +/- 1") for error in errors)
        )
        out[name] = 4 * phase_center.exp() * (retained + remainder)
    return out


def uniform_moments_tjet(
    delta: TJet,
    t: arb,
    grid: int,
    calibration: TJet,
) -> dict[str, TJet]:
    totals = {name: tjet(0) for name in ("KD", "KF", "HDD", "HDF")}
    width = arb("1.2") / grid
    for i in range(grid):
        for j in range(grid):
            values = centered_cell_tjet(
                delta,
                t,
                width * i,
                width * (i + 1),
                width * j,
                width * (j + 1),
                calibration,
            )
            for name, value in values.items():
                totals[name] += value
    return totals


def _wire_tjet(value: TJet) -> tuple[tuple[str, str], ...]:
    return tuple(_wire_arb(component) for component in value.derivatives())


def _unwire_tjet(value: tuple[tuple[str, str], ...]) -> TJet:
    return TJet(*(_unwire_arb(component) for component in value))


def _uniform_tjet_row_worker(arguments):
    (
        precision,
        delta_wire,
        t_wire,
        grid,
        row_start,
        row_stop,
        calibration_wire,
    ) = arguments
    ctx.prec = precision
    delta, t = _unwire_tjet(delta_wire), _unwire_arb(t_wire)
    calibration = _unwire_tjet(calibration_wire)
    totals = {name: tjet(0) for name in ("KD", "KF", "HDD", "HDF")}
    width = arb("1.2") / grid
    for i in range(row_start, row_stop):
        for j in range(grid):
            values = centered_cell_tjet(
                delta,
                t,
                width * i,
                width * (i + 1),
                width * j,
                width * (j + 1),
                calibration,
            )
            for name, value in values.items():
                totals[name] += value
    return {name: _wire_tjet(value) for name, value in totals.items()}


def parallel_uniform_moments_tjet(
    delta: TJet,
    t: arb,
    grid: int,
    calibration: TJet,
    workers: int = 4,
) -> dict[str, TJet]:
    if workers < 1 or grid % workers:
        raise ValueError("grid must be divisible by the positive worker count")
    step = grid // workers
    arguments = [
        (
            ctx.prec,
            _wire_tjet(delta),
            _wire_arb(t),
            grid,
            worker * step,
            (worker + 1) * step,
            _wire_tjet(calibration),
        )
        for worker in range(workers)
    ]
    with ProcessPoolExecutor(max_workers=workers) as executor:
        pieces = list(executor.map(_uniform_tjet_row_worker, arguments))
    totals = {name: tjet(0) for name in ("KD", "KF", "HDD", "HDF")}
    for piece in pieces:
        for name, value in piece.items():
            totals[name] += _unwire_tjet(value)
    return totals


def assemble_y_tjet(moments: dict[str, TJet], delta: TJet) -> TJet:
    numerator = (
        moments["KD"] * moments["HDF"] - moments["KF"] * moments["HDD"]
    )
    return 4 * delta**-4 * numerator / moments["KD"]**2


def centered_half_second_enclosure(
    delta_lo: arb,
    delta_hi: arb,
    t: arb,
    center_grid: int,
    variation_grid: int,
    calibration_coefficients: tuple[arb, arb, arb],
    workers: int = 1,
) -> tuple[arb, TJet, TJet]:
    """Enclose one half of Y'' on a positive delta box."""

    if not arb(0) < delta_lo <= delta_hi:
        raise ValueError("S2 centred delta box must be positive and ordered")
    center, radius = (delta_lo + delta_hi) / 2, (delta_hi - delta_lo) / 2
    center_delta = tjet(center, 1)
    whole_delta = tjet(hull(delta_lo, delta_hi), 1)
    center_calibration = calibration_tjet(
        center_delta, center, calibration_coefficients
    )
    whole_calibration = calibration_tjet(
        whole_delta, center, calibration_coefficients
    )
    integrate = (
        uniform_moments_tjet
        if workers == 1
        else lambda delta, t, grid, calibration: parallel_uniform_moments_tjet(
            delta, t, grid, calibration, workers=workers
        )
    )
    center_y = assemble_y_tjet(
        integrate(center_delta, t, center_grid, center_calibration), center_delta
    )
    whole_y = assemble_y_tjet(
        integrate(whole_delta, t, variation_grid, whole_calibration), whole_delta
    )
    error = (
        radius * arb(center_y.d3.abs_upper()) / 2
        + radius**2 * arb(whole_y.d4.abs_upper()) / 4
    )
    enclosure = center_y.d2 / 2 + error * arb("0 +/- 1")
    return enclosure, center_y, whole_y


def uniform_moments(
    delta: arb,
    t: arb,
    grid: int,
    calibration: DeltaJet2,
) -> dict[str, DeltaJet2]:
    totals = {name: djet(0) for name in ("KD", "KF", "HDD", "HDF")}
    width = arb("1.2") / grid
    for i in range(grid):
        for j in range(grid):
            values = centered_cell(
                delta,
                t,
                width * i,
                width * (i + 1),
                width * j,
                width * (j + 1),
                calibration,
            )
            for name, value in values.items():
                totals[name] += value
    return totals


def _wire_arb(value: arb) -> tuple[str, str]:
    return value.lower().str(90), value.upper().str(90)


def _unwire_arb(value: tuple[str, str]) -> arb:
    return hull(arb(value[0]), arb(value[1]))


def _wire_djet(value: DeltaJet2) -> tuple[tuple[str, str], ...]:
    return tuple(_wire_arb(component) for component in (value.c0, value.c1, value.c2))


def _unwire_djet(value: tuple[tuple[str, str], ...]) -> DeltaJet2:
    return DeltaJet2(*(_unwire_arb(component) for component in value))


def _uniform_row_worker(arguments):
    (
        precision,
        delta_wire,
        t_wire,
        grid,
        row_start,
        row_stop,
        calibration_wire,
    ) = arguments
    ctx.prec = precision
    delta, t = _unwire_arb(delta_wire), _unwire_arb(t_wire)
    calibration = _unwire_djet(calibration_wire)
    totals = {name: djet(0) for name in ("KD", "KF", "HDD", "HDF")}
    width = arb("1.2") / grid
    for i in range(row_start, row_stop):
        for j in range(grid):
            values = centered_cell(
                delta,
                t,
                width * i,
                width * (i + 1),
                width * j,
                width * (j + 1),
                calibration,
            )
            for name, value in values.items():
                totals[name] += value
    return {name: _wire_djet(value) for name, value in totals.items()}


def parallel_uniform_moments(
    delta: arb,
    t: arb,
    grid: int,
    calibration: DeltaJet2,
    workers: int = 4,
) -> dict[str, DeltaJet2]:
    """Deterministic contiguous-row parallelization of a uniform grid."""

    if workers < 1 or grid % workers:
        raise ValueError("grid must be divisible by the positive worker count")
    step = grid // workers
    arguments = [
        (
            ctx.prec,
            _wire_arb(delta),
            _wire_arb(t),
            grid,
            worker * step,
            (worker + 1) * step,
            _wire_djet(calibration),
        )
        for worker in range(workers)
    ]
    with ProcessPoolExecutor(max_workers=workers) as executor:
        pieces = list(executor.map(_uniform_row_worker, arguments))
    totals = {name: djet(0) for name in ("KD", "KF", "HDD", "HDF")}
    for piece in pieces:
        for name, value in piece.items():
            totals[name] += _unwire_djet(value)
    return totals


def assemble_y(
    moments: dict[str, DeltaJet2], delta: arb
) -> DeltaJet2:
    """Exact normalized carrier Y from calibrated physical moments."""

    delta_jet = djet(delta, 1, 0)
    numerator = (
        moments["KD"] * moments["HDF"] - moments["KF"] * moments["HDD"]
    )
    return 4 * delta_jet**-4 * numerator / moments["KD"]**2


def check() -> None:
    derivatives = scaled_bessel_derivatives(arb("30 +/- 1"), "A", 7)
    assert len(derivatives) == 8
    print("S2 exact delta-two/spatial-five infrastructure OK; no promotion")


if __name__ == "__main__":
    check()
