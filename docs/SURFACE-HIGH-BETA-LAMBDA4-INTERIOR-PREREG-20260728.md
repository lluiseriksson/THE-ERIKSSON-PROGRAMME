# High-beta interior absolute-moment splice at lambda four

**Registered:** 2026-07-28, before the terminal Arb sweep

**State:** analytic contract frozen; no certificate result

## Domain and role

Let

```text
beta>=1000/9,
lambda=beta(pi-t)>=4,
p=sin(t/4), c=cos(t/4).
```

The fixed-gap lane already covers `p<=101/200`.  This contract covers the
remaining range `p>=101/200`.  It is designed to combine with the separate
G5 strip `lambda<=4`.

## Principal-square mass chains

On `B=[-6/5,6/5]^2`, put

```text
P=sin^2(s/2), Q=sin^2(alpha/2),
e=sin^2(3/5), k=e/(6/5)^2,
w=P+Q-PQ/q^2,
ell(q)=1-e/(2q^2).
```

For every `q>=101/200`,

```text
ell(q)(P+Q)<=w<=e,
P,Q>=k*s^2,k*alpha^2,
P,Q<=(s^2,alpha^2)/4.
```

The inequalities follow from `2PQ<=e(P+Q)` and a boundary check of the
bilinear function `w`.  The global Bessel upper bound and the lower
companion therefore give explicit normalized bounds

```text
L(q,beta) <= beta^(3/2)e^(-4 beta q) integral_B KD,
beta^(3/2)e^(-4 beta q) integral_B KD <= U(q).
```

The exact formulas are frozen in the executable.

## Dimensionless moment ledger

Symmetry permits replacing `F` by its symmetrization.  For the absolute
ledger it is enough to use

```text
|F|<=A(q)P,
```

where `A(q)` is the maximum at the four corners of the affine-bilinear
coefficient `F/P`.  With `H_B/K<=1/(2 beta z)` and the exact minimum of
`R_q^2/4=q^2(1-P-Q)+PQ` at a rectangle corner, freeze

```text
beta |muF/muD| <= R(q),
beta^2 nuD/muD <= H(q),
beta^3 |nuF/muD| <= W(q),
|X(q)| <= 4[W(q)+R(q)H(q)].
```

No products in the determinant are separated until after these normalized
ratios have been formed.

## Mirror mass ratio

The exact involution gives

```text
rho=exp(-4 beta(c-p))*a_p/a_c.
```

Use `a_p<=U(p)` and `a_c>=L(c,beta)`.  The constrained domain is swept in
`x=pi-t`:

```text
0<=x<=4/(1000/9): beta=4/x,
4/(1000/9)<=x<=103/100: beta=1000/9.
```

The first segment uses

```text
4 beta(c-p)
 =16 sqrt(2) sin(x/4)/x
 >=4 sqrt(2)(1-x^2/96).
```

The second uses the direct monotone sine lower endpoint.  The rational
upper `103/100` slightly enlarges the true `p>=101/200` range.

## Terminal judge

Let `R_p,H_p,X_p` be the maxima on
`q in [101/200,1/sqrt(2)]` and `R_c,H_c` the maxima on
`q in [1/sqrt(2),sqrt(1-(101/200)^2)]`.  If `rho_*` is the constrained
mass-ratio maximum, the exact mirror identity gives the absolute adverse
bound

```text
A_* =
 rho_*/(1-rho_*)^2 * 4(R_p+R_c)(H_p+H_c)
 +rho_*/(1-rho_*) * X_p.
```

The frozen terminal target is

```text
rho_*<1/100,
A_*<3/4.
```

Together with `X_main>=0`, the third-block rest bound `<1/100000`, and
`Q>19/20`, this would give

```text
Q+X_full > 19/20-3/4-1/100000 > 0.
```

The sweep uses 800 rational boxes in each independent `q` range, 64 boxes
on the moving `x` segment, 512 on the fixed-beta segment, and 180-bit Arb.
Any unresolved denominator or non-strict terminal endpoint rejects the
route.
