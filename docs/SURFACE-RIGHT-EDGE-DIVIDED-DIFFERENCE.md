# Right edge without a cubic cancellation: divided differences

## Exact reduction

Put `d=pi-t`, `x=d/2`, and `y=x^2`.  With the shifted correlation from
`SURFACE-RIGHT-EDGE-SHIFTED-CORRELATION.md`, write

```text
S(x)=x U(y).
```

Let

```text
R(d)=sum_{m>=1} (-1)^m I_m(beta)^4 cos(m d),
T(x)=R(2x)=V(y).
```

The exact identities `A(2x)=sin(x)S'(x)-cos(x)S(x)` and
`B(2x)=R'(2x)` give

```text
A(2x)=x^3 a(y),                 B(2x)=x b(y),

a(y)=j(y) U(y)+2 s(y) U_y(y),  b(y)=V_y(y),
s(y)=sin(x)/x,
j(y)=[sin(x)-x cos(x)]/x^3.
```

Both `s` and `j` are entire functions of `y`; their removable values are
`s(0)=1` and `j(0)=1/3`.  Hence

```text
E(pi-2x,beta)=x^2 a(y)/(2 b(y)).
```

Since `lambda=2 beta x=2x/delta`, differentiation yields the quotient-free
sign target

```text
H(lambda,delta)=-E_t/lambda
 = delta/4 * P(y)/b(y)^2,

P(y)=a(y)b(y)+y[a_y(y)b(y)-a(y)b_y(y)].
```

For positive `delta`, `H>0` is therefore equivalent to `P>0` once the
already proved `B>0` gives `b>0`.  The formula extends to `delta=0` after
the usual common saddle scaling.  Most importantly, `P` has no forced
power of `lambda`: the cubic zero of `A`, the linear zero of `B`, and the
third-order zero of the old moment numerator have all been removed before
interval evaluation.

The five non-elementary inputs are exactly

```text
U, U_y, U_yy, V_y, V_yy.
```

No `kt`, `hdd`, or `hdf` moment is required in this lane.

## Cancellation-free integral formulas for U

Let

```text
f(u)=g(pi/2-u),   g(u)=I_1(2 beta cos u)/2,
S(x)=(2/pi) integral_0^pi f(u)g(u-x) du.
```

The exact oddness `S(-x)=-S(x)` and the fundamental theorem of calculus
give

```text
U(y)=-(1/pi) integral_0^pi integral_{-1}^1
       f(u) g'(u+r x) dr du.
```

Differentiating with respect to `y`, and subtracting the terms whose odd
`r` moments vanish, gives formulas that remain regular at `x=0`:

```text
U_y(y)=-(1/(2 pi)) integral f(u) integral_{-1}^1 r^2
         integral_0^1 g'''(u+theta r x) dtheta dr du,

U_yy(y)=-(1/(4 pi)) integral f(u) integral_{-1}^1 r^4
          integral_0^1 theta^2 integral_0^1
          g'''''(u+phi theta r x) dphi dtheta dr du.
```

These identities use only the fundamental theorem of calculus.  No
Taylor polynomial and no unbounded derivative remainder is hidden in
them.

## Cancellation-free formulas for b and b_y

Define the even autocorrelation

```text
C(z)=(1/(2 pi)) integral_0^{2 pi} k(u)k(u+z) du,
k(u)=sum_{m in Z} I_|m|(beta)^2 exp(i m u).
```

Fourier orthogonality gives

```text
C(z)=I_0(beta)^4+2 sum_{m>=1} I_m(beta)^4 cos(mz),
T(x)=[C(pi+2x)-I_0(beta)^4]/2.
```

As `T` is even, the fundamental theorem of calculus yields

```text
b(y)=V_y(y)=T'(x)/(2x)
    =(1/2) integral_0^1 T''(r x) dr,

b_y(y)=(1/4) integral_0^1 r^2 integral_0^1
         T''''(theta r x) dtheta dr.
```

The second display uses `T'''(0)=0` before division by `x`.

## Certificate contract

A terminal small-`lambda` certificate must:

1. verify the algebra in the companion symbolic auditor;
2. enclose the five integral families above on an exact adjacent cover of
   `0<=lambda<=3/2`, `0<=delta<=1/125`;
3. apply the common two-saddle exponential scaling before forming any
   Bessel value;
4. assemble `a`, `a_y`, `b`, `b_y`, and then `P` on each box, requiring
   `b>0` and `P>0`;
5. bound the spatial complement at the level of the five divided-
   difference integrands (or directly at the level of `P`), never by
   independent absolute errors for the old five moments;
6. include the analytic `delta=0` face and overlap the existing paired
   moment lane on a nonempty rational lambda interval.

Status: **exact reduction and analytic design**.  The five-family Arb cover
and its compatible tail are still required; G5 remains open.
