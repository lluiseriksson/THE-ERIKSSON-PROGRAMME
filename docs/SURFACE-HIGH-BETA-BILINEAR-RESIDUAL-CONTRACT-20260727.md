# Surface high-beta bilinear residual contract

**Registered:** 2026-07-27

**State:** exact algebra proved; numerical/analytic inequality open

## Purpose

The high-beta identity has now been reduced to

```text
E'/(-S/2) = Q + X_full,
Q > 19/20,
X_main > 0.
```

It remains to prove `X_full>-19/20`.  Bounding
`abs(X_full-X_main)` by expanding six independent products is wasteful and
also easy to do incorrectly because the full and main denominators differ.
This record fixes the exact cancellation-preserving contract.

## Exact grouping

Write the main moments as

```text
a=muD_main, f=muF_main, u=nuD_main, w=nuF_main
```

and their mirror counterparts as

```text
b=muD_mirror, g=muF_mirror, v=nuD_mirror, x=nuF_mirror.
```

Let `d=a+b=muD_full` and `r=f/a`.  Direct expansion gives

```text
X_full
 = (a/d) X_main
 + (4 beta^3/d) (x-r v)
 + (4 beta^3 (u+v)/d^2) (b r-g).
```

This form divides by neither `b` nor `g`; both can be exponentially small.
The executable SymPy audit is
`scripts/verify_surface_high_beta_bilinear_residual.py`.

## Sufficient unilateral contract

The K2 denominator is positive, the signed full mass gives `d>0`, and the
K2 implication audit proves `X_main>=0`.  Therefore the first term above is
nonnegative.  It is enough to certify

```text
adverse :=
    (4 beta^3/d) (r v-x)
  + (4 beta^3 (u+v)/d^2) (g-b r)
  < 19/20
```

on

```text
beta >= 1000/9,
0 < t <= pi-3/(2 beta).
```

Together with `Q>19/20`, this gives `Q+X_full>0`, hence `E'<0`.
The strict inequality is the only remaining high-beta scalar judge.

## Denominator-change trap

The alternative six-product expansion is

```text
R = a x+b w+b x-f v-g u-g v,
X_full = (a/d)^2 X_main + 4 beta^3 R/d^2.
```

Consequently

```text
X_full-X_main
 = 4 beta^3 R/d^2 - X_main*b*(2a+b)/d^2.
```

The last term is mandatory.  Any purported audit of
`abs(X_full-X_main)` that only bounds `R` has silently replaced `a^2` by
`d^2` and is invalid.

## Why the grouping matches the seven-carrier architecture

The seven nontrivial moments are exactly

```text
f,u,w,b,g,v,x.
```

The first group `x-rv` compares the mirror `F` and `D` moments after
centering by the main ratio.  The second group `br-g` compares the same
ratio at the mass level.  Thus the known corner identity
`|F_mirror-4C|<=6 rho^2` can act before absolute values are taken.

K4's local seven-fraction rows do not automatically prove the displayed
`adverse` inequality: their derivatives, weights, domain union, and overlap
must be assembled into this exact scalar on the complete high-beta domain.
Until that happens, G2 and the paper seal remain open.
