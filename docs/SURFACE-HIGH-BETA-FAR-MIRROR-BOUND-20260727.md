# Surface high-beta far-mirror bound

**Registered:** 2026-07-27

**Corrected:** 2026-07-27 to separate `B union B'` from the rest

**State:** analytic mirror perturbation bound with executable scalar
arithmetic; third-block rest perturbation independently certified

## Domain

Let

```text
beta >= beta0 = 1000/9,
p=sin(t/4) <= p0=101/200,
c=sqrt(1-p^2).
```

Exact rational squaring gives

```text
c-p > 7/20.
```

Indeed

```text
1-(101/200)^2 > (101/200+7/20)^2.
```

## Main and pure-mirror moment bounds

Normalize every moment by the common positive main-saddle scale
`beta^(3/2) exp(-4 beta c)`.  On the main square, the standard kernel
bounds and the pointwise polynomial bounds give

```text
|a| <= 160 beta^(5/2),
|f| <= 480 beta^(5/2),
0<=u <= 40 beta^(3/2),
|w| <= 120 beta^(3/2).
```

On the mirror square the exact involution supplies the relative factor

```text
epsilon=exp(-4 beta(c-p)),
```

and hence

```text
|b| <= 160 beta^(5/2) epsilon,
|g| <= 480 beta^(5/2) epsilon,
0<=v <= 40 beta^(3/2) epsilon,
|x| <= 120 beta^(3/2) epsilon.
```

Here `b,g,v,x` refer only to `B'`.  They do not include the rest.

## Denominator-safe `B union B'` assembly

Let `d1=a+b`.  The full signed mass and the independent rest bound give

```text
d1 > 0.49,
```

so the exact two-block identity can be bounded without substituting the
full-torus denominator.  Repeating the conservative moment arithmetic with
the `0.49` denominator gives

```text
|X_(B union B')-X_main|
 <= 300000000000 beta^12 epsilon.
```

The enlarged constant deliberately absorbs the small denominator change
from the earlier provisional `1/2` calculation.

Since `c-p>7/20`,

```text
|X_(B union B')-X_main|
 < 3e11 beta^12 exp(-(7/5)beta).
```

The right-hand side decreases for `beta>=1000/9`; its outward-rounded value
at the endpoint is below `1e-30`.  The scalar arithmetic is checked by
`scripts/verify_surface_high_beta_far_mirror_bound.py`.  That executable
does not derive the four displayed moment inequalities: those are analytic
inputs proved in the manuscript's saddle/mirror estimates.  It verifies
their exact two-block assembly, denominator safety, rational gap, endpoint
monotonicity, and outward-rounded final margin.

## Add the third block

The exact three-block identity is verified by
`scripts/verify_surface_three_block_decomposition.py`.  Its independent
Abel-layer estimate proves that adding the rest changes the favorable
main-plus-mirror lower bound by less than

```text
1/100000
```

on the entire high-beta domain; see
`scripts/verify_surface_high_beta_rest_perturbation_bound.py`.

Therefore in this far zone, `X_main>=0` implies

```text
X_full > -1/100000 - 1e-30.
```

Together with `Q>19/20`, this closes the far-zone high-beta sign.  The
complementary near zone still requires the principal-ratio certificate
recorded in `SURFACE-HIGH-BETA-RATIO-REDUCTION-20260727.md`.
