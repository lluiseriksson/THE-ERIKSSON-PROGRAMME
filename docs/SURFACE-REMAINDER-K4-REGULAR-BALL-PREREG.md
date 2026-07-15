# K4 regular-ball route: pre-registration

**State:** `TRANSPORT_IDENTITY_FIXED`; `HALF_POWER_AUDIT_PASS`;
`REAL_COERCIVITY_PASS`; `COMPLEX_DISK_PASS`; `POISSON_ORACLE_PASS`;
`NO_K4_PROMOTION`

This document is registered before any regular-ball interval page is read.
It replaces the rejected idea that a pointwise physical second derivative
becomes regular merely by writing `s=sqrt(delta)*sigma` and
`alpha=sqrt(delta)*tau`.

## The transport obstruction

Write `f(delta,s,alpha)=g(delta,sigma,tau)` and let

```text
D = partial_delta at fixed (sigma,tau),
E = sigma partial_sigma + tau partial_tau.
```

Then, at fixed physical `(s,alpha)`,

```text
partial_delta = D - E/(2 delta),
partial_delta^2 = D^2 - ED/delta
                  + E/(2 delta^2) + E^2/(4 delta^2).
```

The executable monomial identity is
`scripts/surface_remainder_k4_transport.py`.  Omitting any of the three
Euler transport terms is a terminal implementation error.  In particular,
pointwise physical second derivatives need not be uniformly bounded in the
scaled chart.

## Coordinate-free replacement of the majorant

The target itself is unchanged.  For a fixed physical carrier mass `H`, a
valid change of variables gives, after the spatial tail is included,

```text
H(delta) = delta * integral g(delta,sigma,tau) d sigma d tau,
H''(delta) = 2 integral Dg + delta integral D^2 g.
```

K4 may therefore be proved by a scaled-cell majorant of the last integrand.
This is an alternative sufficient majorant for the same `H''`, not permission
to replace the literal S1''' weighted union judge.  The final union must still
enclose the entire physical integral, including all chart boundaries and
outer tails.

## Exact Bessel representation

For integer `nu=0,1`, use only

```text
exp(-z) I_nu(z)
 = (sqrt(delta)/pi) integral_0^(pi/sqrt(delta))
     exp(-4 c sqrt(1-delta A) S(delta,phi))
     cos(nu sqrt(delta) phi) d phi,

A = w/delta,
S(delta,phi) = 2 sin^2(sqrt(delta) phi/2)/delta.
```

Here `w` is the exact rationalized saddle deficit.  On a fixed scaled ball,
`A`, `S`, the square root, and the cosine have integer-power delta series.
No derivative of a large-`z` asymptotic remainder is admissible.  The
`phi` split is fixed in scaled `phi`, never in the moving physical angle.

The finite head must be evaluated coefficient-wise with explicit polynomial
arithmetic.  Its Taylor remainder must come from an analytic complex-disk
majorant or an exact integral remainder.  The `phi` tail and the spatial tail
must be bounded by closed Gaussian/incomplete-Gamma expressions, including
their first two delta derivatives and every moving-upper-limit boundary term.

## Gates before implementation

1. **Half-power audit.** Derive the exact leading delta power of each of the
   seven *integrated* carrier masses.  This gate now passes in
   `surface_remainder_k4_half_power_audit.py`: the scaled `A` and `B` Bessel
   factors carry powers `3/2` and `5/2`; after the Jacobian, beta prefactors,
   and the exact first-order zero of the main `f`, every full mass has integer
   valuation zero.  This excludes an uncancelled half-power obstruction; it
   does not supply coefficient or tail bounds.
2. **Complex-domain gate.** Prove `|delta A| <= 1-eta` on the chosen complex
   delta disk and a positive real coercivity constant on both main and mirror
   charts.  The real half now passes at the registered stress value on
   `delta<=1/15`, scaled radius `R=4`, in
   `surface_remainder_k4_real_coercivity.py`.  The complex-disk half also
   passes on the conservative scaled square `|sigma|,|tau|<=4` for
   `|delta|<=7/100` in `surface_remainder_k4_complex_disk.py`; the outward
   majorant keeps `|delta A|<1` for both saddles.  An absent tail overlap still
   rejects the route.
3. **Representation oracle.** Independently enclose the Poisson integral and
   `exp(-z) I_nu(z)` at at least three exact stress arguments.  This is an
   identity audit, not the K4 certificate.  The oracle now passes for
   `z=30,50,800` and `nu=0,1` in
   `verify_surface_remainder_k4_poisson.py`; the composite interval integral
   overlaps Arb's independent Bessel evaluation in all six cases.
4. **Transport oracle.** Finite differences at a positive stress point must
   reproduce all Euler transport terms.  Agreement with naive `D^2 g` is a
   failure signal.
5. **Overlap gate.** On the positive range, the new enclosure and a repaired,
   isolated physical-coordinate enclosure must overlap for the same `H''`.
6. **Convergence gate.** Halving spatial and delta radii must contract the
   design majorant at the registered rate before a production partition is
   frozen.

Only after gates 1--6 pass may a production driver, dependency ledger,
literal seven-row S1''' validator, and independent rerun be created.  Until
then `(H_cube)`, K4, G1, and the sharpened `M_sharp` clause remain open.
