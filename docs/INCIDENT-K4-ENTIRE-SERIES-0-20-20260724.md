# K4 entire-series extension probe — 2026-07-24

Status: `DESIGN_ONLY`; no K4, `S1'''/S2'''`, G2, or G6 promotion.

## Probe

The isolated module `scripts/surface_bessel_entire_0_20.py` evaluates the
positive entire series for

```text
exp(-z) I_1(z)/z,  exp(-z) I_2(z)/z^2
```

with an explicit geometric tail (160 terms).  Point checks at
`z=0.1,4,8,12,16,20` and an 80-cell interval sweep below `z=20` passed for
both families and derivatives through order four.

## K4 insertion result

Monkey-patching both K4 carrier layers to use the extended branch removes the
previous `z<20` rejection, but does not produce a certificate.  Near the
geometric zero set of the radius, interval boxes for `R^2` contain zero and
the ordinary jet for `sqrt(R^2)` divides by the interval radius.  The result
is either non-finite on corner cells or an enclosure many orders too wide
(`worst weighted fraction` about `2.9e15` on the stress strip).

Thus extending the Bessel enclosure alone is insufficient.  A terminal route
needs a corner chart/positive polynomial factorization for the radius (or an
equivalent direct enclosure of the complete carrier) before the low-z branch
can enter the weighted judge.
