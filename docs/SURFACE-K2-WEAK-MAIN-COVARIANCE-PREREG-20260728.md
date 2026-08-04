# Weak main-saddle covariance certificate — preregistration (2026-07-28)

**State:** frozen production design; no K2/G2/G6/manuscript promotion.

## Exact target and identity

For the principal square, with the common positive normalization already
used by the high-beta relay, put

```text
dP = K D dx / KD,
A  = F/D,
R  = (H/K)D.
```

Then

```text
X_main
 = 4 (KD HDF - KF HDD)/KD^2
 = 4 Cov_P(A,R).
```

This certificate targets only

```text
X_main >= -1/20.
```

It does not target the withdrawn sharper assertion `X_main>=0`.

## Centering without an interval quotient

Let `r0=1/(4c)` and use `G=R-r0`.  The determinant is unchanged.  The
implementation does not multiply an interval enclosure of `H/K` back by
`K`.  With `Arel,Brel` the true relative modified-Bessel companions and
`root=sqrt(1-delta*w)`, it forms the exact common numerator

```text
Crel = Brel*D - 2*root*Arel
```

and integrates

```text
KD   = K*D,
KF   = K*F,
GDD  = H*D^2 - r0*K*D
     = Hpref*D*Crel*exp(phase),
GDF  = H*D*F - r0*K*F
     = Hpref*F*Crel*exp(phase).
```

At `delta=0`, `Arel=Brel=root=1` and `D=2`, so `Crel=0` exactly on every
spatial box.

## Frozen enlarged domain

The executed cover is the rational superset

```text
0 <= delta <= 9/1000,
21/10 <= t <= 31415927/10000000.
```

This contains the actual common-`x` lane
`lambda=beta(pi-t)>=3`, `p=sin(t/4)>=101/200`.

Use:

```text
delta boxes: 18 equal rational boxes
t boxes:     32 equal rational boxes
fixed scaled square: [0,12]^2
spatial ladder: 24, then 48 intervals per axis
Arb precision: 180 bits
relative companion: order 4, z0=20 integral remainder
sinc^2/delta: 32 explicit terms plus a positive geometric tail
```

For each parameter box, grid 24 is accepted if it proves the terminal
predicate; otherwise the same box is recomputed at grid 48.  Failure at grid
48 rejects the production run.  This ladder and stopping rule are frozen
before reading a result.

The fixed square lies inside every physical square because

```text
12*sqrt(9/1000) < 6/5.
```

## Full physical tail

The omitted physical region is contained in the radial quadrant tail
`r>=12`.  On the full principal chart, use the proved coercivity

```text
phase <= -lambda0*r^2,
lambda0
 = (cmin/2) (1-u) sinc(3/5)^2 > 0,
cmin=sqrt(2)/2, u=sin(3/5)^2.
```

The true order-four companion enclosure supplies a positive uniform
`Arel` bound and a uniform bound on `Brel/Arel`.  Together with

```text
0<D<=2,
|F|<=6r^2,
```

this gives closed positive Gaussian charges for the four missing moments:

```text
0 <= KD_tail <= M_tail,
|KF_tail| <= F_tail,
|GDD_tail| <= G_* M_tail,
|GDF_tail| <= G_* F_tail.
```

The factor four for the four symmetric quadrants is included exactly once in
all core and tail moments.  The tail intervals are added independently; this
is conservative but rigorous.

## Terminal acceptance

For every one of the `18*32=576` parameter boxes:

1. all four core moments and all tail charges are finite;
2. the core `KD` lower endpoint is strictly positive;
3. after adding the tail intervals, the outward lower endpoint of
   `4(KD*GDF-KF*GDD)/KD^2` is strictly greater than `-1/20`.

Production and replay must be byte-identical, have empty stderr, and record
the source head, Python, python-flint, Arb precision, and dependency hashes.

A pass discharges only the weak main-saddle premise in
`SURFACE-HIGH-BETA-WEAK-MAIN-RELAY-PREREG-20260728.md`.  The terminal union,
K4/S1'''/S2''' bookkeeping, final seal, and paper remain separate.
