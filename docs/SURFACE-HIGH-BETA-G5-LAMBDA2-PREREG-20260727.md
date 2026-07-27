# High-beta G5 extension to lambda two

**Registered:** 2026-07-27, before reading any production result

**State:** production/replay pending

## Claim

Certify the exact five-family right-edge sign judge on

```text
delta in [0,9/1000],
lambda=beta(pi-t) in [3/2,2].
```

This strip is adjacent to the already certified G5 half-line
`lambda in [0,3/2]` and lies inside the high-beta domain
`beta>=1000/9`.

## Frozen partition

```text
delta:  8 boxes [i/1000,(i+1)/1000], i=0,...,7,
        plus [8/1000,9/1000]
lambda: 25 boxes [j/50,(j+1)/50], j=75,...,99.
```

Production units contain five adjacent lambda boxes and all nine delta
boxes.  Every one of the 225 cells must prove, with outward-rounded Arb:

```text
B0 > 0,
P0 > 0,
H=P0/(4 B0^2) > 0.
```

## Analytic changes from the old half-line lane

The central five-family identity is unchanged.  The near-chart tail uses
the larger registered factor `exp(2)` instead of `exp(3/2)`.  The
low-argument integral companion is used because the largest inverse
argument slightly exceeds the old `z>=20` lane while remaining in the
proved `z>=4` lane.  At the frozen maximum,

```text
eta_max = delta_max*lambda_max/2 = 9/1000 < 1/100 < 3/80,
```

so the previously proved finite chart and exterior-gap geometry remains
valid.

## Promotion rule

No result is promoted from a single unit.  Promotion requires:

1. all five production units,
2. five independently executed replay units,
3. exact parsed-row equality,
4. exact delta/lambda adjacency with no duplicates,
5. current dependency hashes and one source head,
6. a seam audit at `lambda=3/2`.

Any nonpositive lower endpoint rejects this route.
