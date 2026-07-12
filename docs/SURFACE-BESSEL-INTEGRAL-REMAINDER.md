# Integral-form remainder for the scaled Bessel factors

**State:** exact lemma implemented; not by itself a G1/G2 certificate.

The divergent absolute coefficient fold in the old saddle expansion is not
used.  For `z>0`, the standard integral representation and
`u=z(1-x)` give

```text
A(z) = exp(-z) I_1(z)/z
     = sqrt(2)/(pi z^(3/2))
       integral_0^(2z) exp(-u) u^(1/2) (1-u/(2z))^(1/2) du,

B(z) = exp(-z) I_2(z)/z^2
     = 2^(3/2)/(3 pi z^(5/2))
       integral_0^(2z) exp(-u) u^(3/2) (1-u/(2z))^(3/2) du.
```

For `alpha` equal to `1/2` or `3/2`, write

```text
(1-x)^alpha = sum_{k=0}^N c_k x^k + R_N(x),
c_k = (-1)^k binom(alpha,k).
```

On `0<=x<=1/2`, consecutive absolute terms have ratio below `1/2`,
so

```text
|R_N(x)| <= 2 |c_(N+1)| x^(N+1).
```

After splitting the integral at `u=z` and completing the polynomial
moments to infinity, the absolute error in the unscaled integral is at most

```text
2 |c_(N+1)| Gamma(p+N+2)/(2z)^(N+1)
+ Gamma(p+1,z)
+ sum_{k=0}^N |c_k| Gamma(p+k+1,z)/(2z)^k,
```

where `(p,alpha)=(1/2,1/2)` for `A` and `(3/2,3/2)` for `B`.
No asymptotic equality is used.  If an elementary expression is preferred,

```text
Gamma(a,z) <= exp(-z) z^a/(z-a+1),   z>a-1,
```

because `(1+v/z)^(a-1) <= exp((a-1)v/z)` after `u=z+v`.

After division by the leading complete moment, both families have the
common form

```text
A(z) = (2 pi)^(-1/2) z^(-3/2) (P_A,4(1/z) + eps_A),
B(z) = (2 pi)^(-1/2) z^(-5/2) (P_B,4(1/z) + eps_B),
|eps_family| <= C_family/z^5                 (z>=20).
```

The constants are computed with outward rounding at `z=20`.  This is a
half-line statement, not a grid inference: after multiplication by `z^5`,
each elementary far-tail term is proportional to
`exp(-z) z^(p+6)/(z-p-k)`, whose logarithmic derivative is negative for
the declared orders and `z>=20`; the local binomial remainder is already
exactly proportional to `z^(-5)`.

The same file performs a controlled quotient.  If `P_A`, `P_B` are the
two relative polynomials and `Q_4` is the exact formal quotient through
degree four, then

```text
P_B - P_A Q_4 = h^5 R(h),       h=1/z.
```

On the whole interval `0<=h<=1/20`, interval evaluation of `R`, `Q_4`,
the two value remainders, and a positive lower bound for
`P_A-C_A h^5` gives one explicit `C_ratio` such that

```text
| z B(z)/A(z) - Q_4(1/z) | <= C_ratio/z^5,   z>=20.
```

Thus the ratio division is an inequality between convergent enclosures,
not a formal division of two unbounded asymptotic tails.

`scripts/surface_bessel_integral_remainder.py` evaluates these bounds with
outward-rounded Arb arithmetic and checks them against the defining Bessel
functions.  It also obtains derivatives through order four from the exact
Bessel differential recurrences and
`exp(-z)I_0(z)=z^2 B(z)+2A(z)`.  Thus no derivative of an error estimate is
taken.  The next terminal step is to propagate these regular value/jet
enclosures through the common saddle carrier and its delta derivatives;
until that propagation and uniform integration are complete, `(H_tail)` and
`(H_cube)` remain open.
