# Exact half-line positivity of the cubic endpoint coefficient

**State:** proved analytic lemma; constant arithmetic executable.  This
closes the sign of the cubic endpoint coefficient for `beta>=125`.  It does
not by itself control the finite `d<=3/(2 beta)` remainder, so G5 remains
open until that separate radius estimate is supplied.

Let

```text
f(x) = I_1(x)/2,
y = 2 beta sin(u),
z = 2 beta cos(u),
g(u) = f(z).
```

The exact parity lemma in the manuscript gives

```text
c3 = (S3-S1)/24 = (1/(6 pi)) integral_0^(pi/2) J(u,beta) du,
J = g'(pi/2-u)(-g''(u)) - g(pi/2-u)g'(u).
```

Direct differentiation yields

```text
J = -z^2 f'(y)f'(z) + z y^2 f'(y)f''(z) + y f(y)f'(z).
```

Put `ell(x)=f'(x)/f(x)`.  The modified-Bessel equation
`f''+(1/x)f'-(1+1/x^2)f=0` and `y^2+z^2=4 beta^2` give the exact regular
form

```text
J = f(y)f(z) beta^3 H,
H = 8 sin(u)^2 cos(u) ell(y)
    + beta^(-2) [2 sin(u)^2 ell(y)/cos(u)
                  + 2 sin(u) ell(z)]
    - 4 beta^(-1) ell(y)ell(z).
```

## Positive central block

On `C=[pi/8,3pi/8]` and `beta>=125`, both `y,z>375/4`.  The Amos lower
bound at order one and strict order monotonicity give

```text
I_2(x)/I_1(x) > 97/100,
97/100 < ell(x)=I_2(x)/I_1(x)+1/x < 51/50.
```

Indeed the Amos bound is
`I_2/I_1 >= x/(2+sqrt(x^2+4))`; using
`sqrt(x^2+4)<x+2/x` and `x>=375/4` makes its right side exceed
`97/100`.  The upper inequality uses `I_2/I_1<1` and
`1/x<=4/375<1/50`.

Since both sine and cosine exceed `3/8`, dropping the two positive
`beta^(-2)` terms gives

```text
H > (27/64)(97/100) - (4/125)(51/50)^2 > 3/8.
```

Use only the inner interval `I=[3pi/16,5pi/16]`.  There `y,z>=beta`, and
the already proved global lower companion

```text
I_1(x) >= exp(x)/sqrt(2 pi x) (1-0.6/x),  x>=10,
```

implies

```text
f(y)f(z) >= exp(y+z)/(16 pi beta) (622/625)^2.
```

Moreover `sqrt(2)>707/500`, `cos(pi/16)>49/50`, hence
`sin(u)+cos(u)>277/200` on `I`.  Therefore

```text
integral_I J du
  > (3/1024)(622/625)^2 beta^2 exp(277 beta/100).
```

## Absolute exterior block

For every integer `n>=0` and `x>=0`, the standard integral representation
gives `I_n(x)<=exp(x)`.  Consequently

```text
f(x)<=exp(x)/2,  f'(x)<=exp(x)/2,  f''(x)<=exp(x)/2.
```

On the exterior `X=[0,pi/8] union [3pi/8,pi/2]`, whose total length is
`pi/4`, the exact formula for `J` gives

```text
|J| <= (7/2) beta^3 exp(y+z).
```

There `sin(u)+cos(u)<131/100`, so

```text
integral_X |J| du < (7 pi/8) beta^3 exp(131 beta/50).
```

The remaining part `C\I` is nonnegative and may be discarded.  Dividing
the exterior upper bound by the inner lower bound and using `pi<22/7`
gives

```text
exterior/inner < 948 beta exp(-3 beta/20).
```

This function is decreasing for `beta>=125`, and at the endpoint

```text
exp(75/4) > exp(18) > 18^7/7! > 948*125.
```

Thus the exterior magnitude is strictly smaller than the positive inner
mass.  Hence `integral J>0` and therefore

```text
c3(beta) > 0  for every beta>=125.
```

The next G5 obligation is sharply isolated: bound the order-five-and-higher
endpoint remainder strongly enough that the negative cubic term in `W`
dominates for `0<d<=3/(2 beta)`.  No sign asymptotic remains open above
125.
