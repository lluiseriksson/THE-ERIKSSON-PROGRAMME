# Surface high-beta \(Q>19/20\) certificate

**Registered:** 2026-07-27

**State:** proved algebra plus outward-rounded Arb certificate

## Claim

Let

```text
Qratio = <Phi>/<D>.
```

On

```text
beta >= 1000/9,
0 < t <= pi - 3/(2 beta),
```

one has

```text
<Phi> - (19/20)<D> > 0,
Qratio > 19/20.
```

The second statement uses the already proved signed-mass lemma
`<D> >= 1/2`.  The certificate never divides two independently rounded
bounds.

## Algebra

Put

```text
P = sin(s/2)^2,  Q = sin(alpha/2)^2.
```

Kernel symmetry gives

```text
Phi_sym = 2 - 6(P+Q) + 4(P^2+Q^2+PQ),
D       = 2(1-P-Q).
```

Put \(h=19/20\). On the main rectangle,

```text
Phi_sym-hD >= (2-2h)-(6-2h)(P+Q).
```

On the mirror rectangle, in the local variables `P',Q'` and with
`p=sin(3/5)^2`,

```text
Phi_sym-hD
 >= (2+2h)-(12+4h)p+12p^2
  = 0.0823891601... > 0.
```

The polynomial is decreasing in each variable on the registered mirror
square.  The exact alternating Taylor bound
`sin(3/5)^2<8/25` proves both the derivative sign and the positive displayed
minimum.  Finally, in
`x=cos(s), y=cos(alpha)`,

```text
Phi_sym-hD + 1+h^2/3
  = (x-h/3)^2 + (y-h/3)^2 + (x-h/3)(y-h/3)
  >= 0.
```

If `L,G,R` are respectively the existing cascade-1 main-mass lower
bound, main weighted-mass upper bound, and remaining-mass upper bound, then
the mirror rectangle can be discarded as nonnegative and

```text
<Phi>-h<D>
 >= (2-2h)L - (6-2h)G - (1+h^2/3)R.
```

Every term is assembled with the safe endpoint direction.

## Certified domain sweep

`scripts/certify_surface_high_beta_q_half.py` uses 160-bit python-flint/Arb
and the same four analytic charges as `cascade1_floor_arb.py`.

The fixed-\(t\) adverse charges decrease with \(\beta\), while `L`
increases, so the lower boundary is enough.  The executable cover is:

1. 800 rational boxes at `beta=1000/9`;
2. 80 logarithmic boxes on the moving path
   `beta=(3/2)/(pi-t)`;
3. the direct `x=pi-t` enclosure on `0<x<=1/1000`.

The minimum certified lower margin is

```text
0.0144137495465863815...
```

in the last moving-path box.  The enclosure remains strictly separated from
zero.

## Reproduction

```powershell
python scripts/verify_surface_high_beta_q_half_algebra.py
python scripts/certify_surface_high_beta_q_half.py
python -m pytest -q tests/test_surface_high_beta_q_half.py
```

## Scope

This closes the non-bilinear \(Q\)-part of the high-beta sign identity with
the stronger quantitative bound \(Q>19/20\).
The independent executable implication
`scripts/verify_surface_high_beta_main_positive.py` also shows that K2's
certified main carrier is strictly positive for every positive `delta` in
its domain.  Therefore neither the \(Q\)-term nor the main-saddle bilinear
term can obstruct the high-beta sign.

The only remaining obstruction is the full-minus-main bilinear correction.
Consequently it does not yet promote G2 or the final paper seal.
