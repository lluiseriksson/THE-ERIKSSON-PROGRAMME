# K2 degree-eight centered complex supremum — preregistration

**Registered:** 2026-07-28, before evaluating any degree-eight circle arc.

**State:** conditional fixed-square design.  No K2, K4, S1/S2, gate, or
manuscript promotion.

## Entry gate

The expression-level exact checker was nonterminal and is not evidence.
This run is forbidden until both production and replay transcripts from
`check_surface_remainder_delta0_r7_r8_list_targets.py` terminate with
`R7/R8 SPARSE EXACT TARGET CHECK PASS` and print identical exact
`Y0,...,Y7` lines.  The driver enforces that amended gate.  This is
single-engine exact/replayed; independent numerical corroboration remains
mandatory before any K2 promotion.

## Frozen configuration

```text
t = 29/10
rho = 17/2000
delta_max = 1/1000
fixed square = [0,12]^2
relative companion degree = 8
p-over-delta entire-series terms = 18
(spatial grid, theta arcs) ladder = (48,64), (96,128)
Arb/Acb precision = 140 bits
```

The shift-centered covariance assembly and all complex geometry are those
registered in
`SURFACE-K2-FIXED-SQUARE-CENTERED-COMPLEX-SUPREMUM-PREREG-20260728.md`.
No interval from the earlier degree-five run is reused.

## Frozen Cauchy budget

Write the surrogate expansion as

```text
Y(delta) = sum_{k>=0} Y_k delta^k.
```

The theorem's nominal stress-cell allowance is
`theta3*delta^2` after retaining only `Y0+Y1*delta`.  This run charges the
absolute value of

```text
Y2 + Y3*delta + Y4*delta^2 + Y5*delta^3
   + Y6*delta^4 + Y7*delta^5
```

against `theta3`, and applies Cauchy only to the remaining surrogate tail.
With `q=delta_max/rho`, the frozen multiplier is

```text
q^8/(1-q).
```

At the registered stress cell the outward-rounded design values are

```text
available remainder = 1.9657702810764977e-6
Cauchy multiplier   = 4.1591660230052620e-8
required M          = 47.26356847029885.
```

The first ladder level with a strict complex KD-modulus lower bound and
`M_sup < required M` is a conditional fixed-square pass.  Exhaustion is
failure.

## Scope barrier

Even a pass proves only the finite degree-eight polynomial-companion
surrogate on the fixed square at `t=2.9`.  It does not control:

- the true sectorial Bessel-companion remainder on the real delta axis;
- the moving exterior of the rescaled square;
- other t-cells;
- the full K2 or G2 budgets.

Those errors must be bounded separately with outward-rounded real-axis
certificates.  This run may not remove any manuscript slot.
