# Weak-main covariance far lane — preregistration (2026-07-28)

## Logical need

The original weak-main rectangle starts at `t=21/10` because it was designed
for the common-variable lane `p=sin(t/4)>=101/200`.  It does not discharge the
complementary fixed-gap lane.

On that far lane the existing analytic estimate proves

```text
|X_(B union B')-X_main| < 10^-30,
|X_full-X_(B union B')| < 1/100000,
Q > 19/20.
```

Thus the same weak premise gives

```text
Q+X_full
 > 19/20-1/20-10^-30-1/100000
 > 0.89998.
```

No sharp positivity premise is required, but `X_main>=-1/20` must also be
certified here.

## Frozen far rectangle

```text
delta: [0,9/1000], 18 equal rational boxes
t:     [0,21/10], 32 equal rational boxes
core:  [0,12]^2
Arb:   180 bits
grids: 24, then 48, then 96 only on unresolved boxes
target: outward X_main lower > -1/20
```

The endpoint `21/10` is shared exactly with the near rectangle.  Their union
contains `0<=t<=pi` and therefore both `p` lanes without needing a numerical
approximation to `4 asin(101/200)`.

Before freezing the grid ladder, seven representative boxes were run in
design-only mode.  Six passed at grid 24 or 48.  The single failure,
`(delta_index,t_index)=(17,16)`, passed at grid 96 with outward lower endpoint
`-0.0144913023832486...>-1/20`.  These probes carry no theorem load.

Production/replay, dependency validation, and the exact far-lane relay must
all pass before this premise is used by G2.
