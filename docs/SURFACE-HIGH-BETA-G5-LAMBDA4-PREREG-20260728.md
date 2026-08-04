# High-beta G5 extension from lambda two to lambda four

**Registered:** 2026-07-28, before reading any cell with `lambda>2`

**State:** frozen production design; no result

## Claim

Certify the exact five-family right-edge sign judge on

```text
delta in [0,9/1000],
lambda=beta(pi-t) in [2,4].
```

This strip is adjacent to the certified high-beta G5 union
`lambda in [0,2]`.  Its purpose is to move the analytic
main-plus-mirror splice to `lambda=4`, where a denominator-safe absolute
moment bound is designed to close.

## Frozen partition

```text
delta:  9 boxes [i/1000,(i+1)/1000], i=0,...,8
lambda: 100 boxes [j/50,(j+1)/50], j=100,...,199
units:  10 adjacent lambda boxes per unit
```

Every one of the 900 cells must prove with outward-rounded Arb arithmetic

```text
B0>0,
P0>0,
H=P0/(4 B0^2)>0.
```

The coarse partition is `qgrid=80`, `rgrid=16`.  A failing coarse cell is
allowed exactly one frozen mixed refinement:

```text
qgrid=160, rgrid=32,
U3 and B4 angular refinement 8,
all other angular refinements as in the lambda-two certificate.
```

No posterior delta or lambda bisection is allowed in this campaign.

## New tail ledger

The old lambda-two near charge contains `exp(2)` and cannot be reused.
This campaign recomputes the same proved finite-tail formula with
`exp(4)`.  The far charge is unchanged.  The low-argument Bessel companion
remains the proved `z>=4` lane.

At the frozen maximum,

```text
eta_max=delta_max*lambda_max/2=18/1000<3/80,
```

so the finite chart containment and exterior phase-gap hypotheses remain
inside their proved domain.  The driver checks this exact inequality.

## Failure and promotion rules

Any nonpositive lower endpoint terminates the affected unit and rejects
this frozen route.  Promotion requires:

1. all ten production units from one source head;
2. ten fresh replay units from the same source head;
3. exact parsed-row equality;
4. the exact 900-cell rational union with no duplicates;
5. current dependency hashes;
6. exact seams at `lambda=2` and `lambda=4`.

The older, rejected `delta<=1/30` lambda-four design is not evidence for or
against this narrower high-beta campaign; its failure remains preserved.
