# High-beta G5 ratio cover from lambda two to lambda three

**Registered:** 2026-07-28, before any production-cell result

**State:** frozen terminal design

## Claim and partition

Certify the exact five-family right-edge sign judge on

```text
delta in [0,9/1000],
lambda=beta(pi-t) in [2,3].
```

Use

```text
delta:  9 boxes [i/1000,(i+1)/1000], i=0,...,8
lambda: 50 boxes [j/50,(j+1)/50], j=100,...,149
units:  10 adjacent units of 5 lambda boxes
```

Every one of the 450 cells must prove `B0>0` and the
cancellation-preserving ratio `Qratio>0`.

## Exact sign judge

With the scaled five families, put

```text
P0 = A0 B0 + (lambda^2/4)(A1 B0-A0 B1),
Qratio = A0(1-lambda^2 B1/(4 B0)) + lambda^2 A1/4.
```

The executable algebra test requires

```text
P0=B0 Qratio.
```

Thus `B0>0` and `Qratio>0` imply `P0>0` without first subtracting
independent large product intervals.

## Wider central chart and tail

Freeze the central window `|q|<=4`.  At

```text
delta_max=9/1000,
lambda_max=3,
eta_max=27/2000,
```

the executable geometry checks:

1. the moving window stays strictly inside the two angular charts;
2. the Bessel argument has a positive explicit floor and `1/z<1/4`;
3. the central Gaussian rate remains above `4/3`.

For each lambda cell, the near-tail charge uses `exp(lambda_hi)` and
integrates the Gaussian tail from `q=4`; the exterior phase-gap charge is
unchanged.

## Frozen refinement

The coarse evaluator is

```text
side=4, qgrid=128, rgrid=16, thetagrid=4, phigrid=4.
```

If either sign is unresolved, exactly one mixed refinement is allowed:

```text
side=4, qgrid=256, rgrid=32,
U3 and B4 angular refinement 8,
all other angular refinements as in the registered driver.
```

There is no posterior parameter subdivision or tolerance change.

## Promotion rule

Promotion requires ten production units and ten fresh replay units from
one source head, current dependency hashes, exact parsed-row equality,
the exact 450-cell rational union without duplicates, and exact seams at
lambda 2 and 3.  One nonpositive lower endpoint rejects the route.
