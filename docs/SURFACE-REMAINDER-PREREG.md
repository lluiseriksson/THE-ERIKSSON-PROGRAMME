# Surface remainder localization — pre-registration

**Registered:** 2026-07-11, before running a localized S1'''/S2''' certificate
**State:** `DESIGN_GATE`; no theorem or certificate claim

This record replaces the undefined phrase “full-plane true untruncated
integrand” by an exact localized identity.

## Fixed constants

Use `delta=1/beta`, scaled radius `r^2=sigma^2+tau^2`, and

```text
R0 = 4,       R1 = 10,       DeltaR2 = R1^2-R0^2 = 84.
```

Define `chi(r^2)=1` for `r<=R0`, `chi=0` for `r>=R1`, and on the
transition set

```text
q = (r^2-R0^2)/DeltaR2,
chi = 1 - 10 q^3 + 15 q^4 - 6 q^5.
```

The value and first two derivatives agree at both junctions. The support
stays below the first removable-`z=0` point at the worst beta:
`R1=10 < pi*sqrt(15)=12.167...`. Thus the large-`z` endpoint-recurrence
lane can be used on the localized support; any box violating `z>4` must fail
loudly and route to the entire-series lane.

## Exact identity

For a fixed physical chart `D`, its true integrand `f`, and its periodic
formula `f_per`, define

```text
v_core(delta) = integral_R2 chi((s^2+a^2)/delta) f_per(delta,s,a) ds da,

v_comp(delta) = integral_D [1-chi((s^2+a^2)/delta)] f(delta,s,a) ds da
              - integral_(R2\D) chi((s^2+a^2)/delta)
                    f_per(delta,s,a) ds da.
```

Then `v=v_core+v_comp` exactly for every `delta>0`. After
`s=sqrt(delta)*sigma`, `a=sqrt(delta)*tau`, the core has fixed compact
support. The complement remains responsible for all cutoff and exterior
derivatives.

For `u=(s^2+a^2)/delta`,

```text
partial_delta chi(u)   = -(u/delta) chi'(u),
partial_delta^2 chi(u) = [u^2 chi''(u)+2u chi'(u)]/delta^2.
```

These terms are mandatory K4 terms.

## Pre-registered gates

1. `L0`: symbolic checks of C² junctions, the two delta-derivative formulas,
   and the exact core/complement identity.
2. `L1`: all seven core `v_m''` integrands finite under Arb boxes at the
   registered stress cell, using exact recurrences and complete-monotone
   endpoint hulls; no interval box crosses `delta=0`.
3. `L2`: the main-side three core integrals must fit their committed global
   bucket scales on a reproducible refinement ladder. Mirror endpoint raw
   sups are diagnostic only because the final judge is weighted.
4. `L3`: value, first, and second derivatives of both complementary integrals
   receive one uniform integrable envelope. Boundary/cutoff terms may not be
   inferred from mass alone.
5. `L4`: only the literal weighted partition sums S1''' and S2''' can promote
   G1/G2. The partition is born ordered and includes a separate analytic
   `[0,delta_*]` K2 patch.

Measured failure at any gate is terminal for these constants: record it and
choose new constants only in a new pre-registration. A passing L1/L2 smoke is
not a certificate for L3/L4.
