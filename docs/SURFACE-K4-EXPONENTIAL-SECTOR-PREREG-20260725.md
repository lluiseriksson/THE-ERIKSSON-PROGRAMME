# K4 sector-aware exponential modulus — preregistration

Date: 2026-07-25. This is a new design-only experiment following the
rectangular-modulus failure. It does not promote K4, `S1'''/S2'''`, G1, G2,
or G6.

## Frozen domain and partition

Use the same stress parameters as A1: `t=29/10`, complex delta disk radius
`rho=7/100`, scaled radius `R=4`, `Phi=12566371/1000000`, Cauchy radius
`r=59/2000`, Arb-140, and degree cap `N<=16`. Cover the disk by the polar
superset

```text
radius       [0,rho], four equal radial intervals
angle        [0,6283186/1000000], sixteen equal angular intervals
sigma,tau    two equal real intervals each on [-4,4]
phi          sixteen equal intervals on [0,Phi]
```

The principal square-root and entire `sinc` expressions are evaluated by
outward Arb/Acb balls. The polar rectangle is a superset of the disk because
the angular endpoint is an upper rational bound for `2*pi`.

## Acceptance

For each main and mirror saddle, the driver must print the maximum outward
upper bound of the exponent real part and the induced modulus. The same judge
as A1 is frozen:

```text
min_N M_sector*(N+1)*(N+2)*(r/rho)^(N-1)/(1-r/rho)
    < 0.5*(1-0.2758)
```

Any non-finite enclosure or branch ambiguity is a design failure. A pass is
still only a modulus milestone; coefficient heads, both moving tails,
spatial tails, overlap, and t-uniformity remain open.

## Result

The frozen run is archived in
`INCIDENT-K4-BALL-REACH-SECTOR-20260725.md`: the best tail is approximately
`8.85e44199`, so the sector-aware interval implementation fails the strict
judge. No K4 or manuscript state changes.
