# Surface high-beta bilinear residual contract

**Registered:** 2026-07-27

**Corrected:** 2026-07-27, before manuscript promotion

**State:** exact three-block algebra and rest-size inequality proved;
main-plus-mirror ratio signs remain open

## Scope correction

The first version of this record denoted the second moment block by
“mirror” while also writing `d=a+b=muD_full`.  Those statements cannot both
hold: the physical domain is the disjoint union of the main square `B`, its
mirror `B'`, and the rest.  The two-block identity itself was exact, but its
claim to be a full-torus assembly was incomplete.

This correction makes the three blocks explicit.  No result based on the
old abbreviation is promoted to the manuscript.

## Purpose

The high-beta identity is

```text
E'/(-S/2) = Q + X_full,
Q > 19/20,
X_main > 0.
```

It remains to control the passage from `X_main` to `X_full` without
destroying the determinant cancellations or silently changing a
denominator.

## First assembly: main plus mirror only

Write the moments on `B` as

```text
a=muD_B, f=muF_B, u=nuD_B, w=nuF_B
```

and the mirror-chart moments before their signed involution as

```text
a'=muD_chart, f'=muF_chart, u'=nuD_chart, w'=nuF_chart.
```

If `S>0` is the exact mirror scale, then the physical moments on `B'` are

```text
b=-S a', g=-S f', v=S u', x=S w'.
```

Let `d1=a+b`, `r=f/a`, and

```text
X1=4 beta^3 (d1*(w+x)-(f+g)*(u+v))/d1^2.
```

Direct expansion gives

```text
X1
 = (a/d1) X_main
 + (4 beta^3/d1) (x-r v)
 + (4 beta^3 (u+v)/d1^2) (b r-g).
```

With

```text
rho=S a'/a, r'=f'/a', h=u/a, h'=u'/a',
X'=4 beta^3(a'w'-f'u')/(a')^2,
```

the adverse part reduces exactly to

```text
4 beta^3 rho/(1-rho)^2 * (r-r')*(h+h')
 - rho/(1-rho)*X'.
```

This is a statement about `B union B'`, not the full torus.  The executable
audit is `scripts/verify_surface_mirror_cross_decomposition.py`.

## Second assembly: add the rest

Let the rest moments be

```text
e=muD_R, k=muF_R, y=nuD_R, z=nuF_R,
```

and put

```text
d=d1+e, r1=(f+g)/d1.
```

Then the exact full-torus identity is

```text
X_full
 = (d1/d) X1
 + (4 beta^3/d) (z-r1 y)
 + (4 beta^3 (u+v+y)/d^2) (e r1-k).
```

It is verified independently by
`scripts/verify_surface_three_block_decomposition.py`.

## Certified rest budget

Let

```text
L=beta^(3/2) exp(-4 beta c) integral_R K.
```

The already certified Abel-layer majorant from `cascade1_floor_arb.py`,
combined with `c>1/sqrt(2)>7/10`, gives at the worst endpoint
`beta=1000/9`

```text
L < 2.158e-19.
```

The pointwise inequalities

```text
|D|<=2, |F|<=12, H_B<=K/(8 beta)
```

give

```text
|e|<=2L, |k|<=12L, y<=L/(2 beta), |z|<=3L/beta.
```

The signed mass floor gives `d>=1/2`.  Step 0 and the moving-window
inequality give

```text
|muF_full/muD_full|
 <= 29.4/(beta*c)+36 exp(-3/pi).
```

Consequently `d1>0.49`, `|r1|<14.233`, and the absolute value of the two
rest terms in the full-torus identity is

```text
< 4.489e-6 < 1/100000.
```

The endpoint reduction is uniform on `beta>=1000/9`: every layer
contribution to `beta^(9/2)L` and the small-z shard is decreasing there.
All scalar arithmetic is outward-rounded in
`scripts/verify_surface_high_beta_rest_perturbation_bound.py`.

## Remaining unilateral contract

The rest is now below `1/100000`.  Thus the missing high-beta statement is
confined to `B union B'`: prove the two ratio signs that make `X1>=0`,
equivalently the principal-ratio certificate recorded in
`SURFACE-HIGH-BETA-RATIO-REDUCTION-20260727.md`.

Once that certificate is present,

```text
Q + X_full > 19/20 - 1/100000 > 0,
```

and hence `E'<0` throughout the high-beta range.

## Denominator-change trap

Any expansion of `X_full-X_main` must include both assembly steps.  In
particular, bounding only cross-products after replacing a main denominator
by a full denominator is invalid.  Both SymPy audits above retain the
denominator-change terms explicitly and are permanent regression tests.
