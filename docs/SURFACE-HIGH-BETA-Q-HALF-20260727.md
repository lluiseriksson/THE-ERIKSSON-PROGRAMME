# Surface high-beta \(Q>1/2\) certificate

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
<Phi> - <D>/2 > 0,
Qratio > 1/2.
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

On the main rectangle,

```text
Phi_sym-D/2 >= 1-5(P+Q).
```

On the mirror rectangle, in the local variables `P',Q'` and with
`p=sin(3/5)^2`,

```text
Phi_sym-D/2
  = 3-7(P'+Q')+4(P'^2+Q'^2+P'Q')
 >= 3-14p+12p^2
  = -0.2437328188... .
```

The polynomial is decreasing in each variable on the registered mirror
square because `p < (3/5)^2 < 7/12`.  Finally, in
`x=cos(s), y=cos(alpha)`,

```text
Phi_sym-D/2 + 13/12
  = (x-1/6)^2 + (y-1/6)^2 + (x-1/6)(y-1/6)
  >= 0.
```

If `L,G,M,R` are respectively the existing cascade-1 main-mass lower
bound, main weighted-mass upper bound, mirror-mass upper bound, and
remaining-mass upper bound, then

```text
<Phi>-<D>/2
 >= L - 5 G + (3-14p+12p^2) M - (13/12) R.
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
0.575144785494227595...
```

in the first fixed-beta box.  Thus the inequality has substantial slack.

## Reproduction

```powershell
python scripts/verify_surface_high_beta_q_half_algebra.py
python scripts/certify_surface_high_beta_q_half.py
python -m pytest -q tests/test_surface_high_beta_q_half.py
```

## Scope

This closes the non-bilinear \(Q\)-part of the high-beta sign identity.
It does not by itself bound the full-minus-main bilinear correction.
Consequently it does not yet promote G2 or the final paper seal.
