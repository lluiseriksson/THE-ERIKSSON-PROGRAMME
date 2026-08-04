# High-beta interior splice at lambda eighteen-fifths

**Registered:** 2026-07-28, before the terminal Arb sweep

**State:** frozen successor to the certified lambda-four splice

## Claim

Repeat the proved absolute-moment argument of
`SURFACE-HIGH-BETA-LAMBDA4-INTERIOR-RESULT-20260728.md` on the larger domain

```text
beta>=1000/9,
lambda=beta(pi-t)>=18/5,
p=sin(t/4)>=101/200.
```

The fixed-gap certificate still handles `p<=101/200`.

## Frozen changes

All principal-square moment bounds, q partitions, and the third-block rest
bound are unchanged.  Only the constrained mirror-mass sweep changes:

```text
x_split=(18/5)/(1000/9)=81/2500,
4 beta(c-p)>= (18/5)sqrt(2)(1-x^2/96)
```

on the moving segment.  The fixed-beta segment again ends at the rational
superset `x=103/100`.

The terminal targets are

```text
rho<3/200,
absolute main-plus-mirror adverse correction<9/10.
```

Together with `Q>19/20` and rest `<1/100000`, the required final margin is

```text
19/20-9/10-1/100000=0.04999>0.
```

The sweep retains 800+800 q boxes, 64 moving-x boxes, 512 fixed-x boxes,
and 180-bit Arb.  Production and replay must bind one source head and exact
dependency hashes.
