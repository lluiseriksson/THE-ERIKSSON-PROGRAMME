# High-beta G5 local-tail cover to lambda eighteen-fifths

**Registered:** 2026-07-28, before any local-tail cell result

**State:** frozen successor to the failed uniform-`exp(4)` design

## Claim and partition

Certify

```text
delta in [0,9/1000],
lambda in [2,18/5].
```

Use the same nine delta cells and lambda width `1/50`:

```text
delta_index=0,...,8,
lambda_index=100,...,179.
```

Eight production units contain ten adjacent lambda cells each.  Every one
of the 720 cells must prove `B0>0`, `P0>0`, and `H>0`.

## Sole ledger change

For a cell `[lambda_lo,lambda_hi]`, the proved near-tail formula is charged
with

```text
exp(lambda_hi)
```

instead of the rejected global `exp(4)`.  This is valid because the angular
shift exponent is monotone in lambda and `lambda<=lambda_hi` on the entire
cell.  The far tail, low-argument companion, central integrals, coarse
partition, and one allowed mixed refinement are unchanged.

At the global endpoint

```text
delta_max*lambda_max/2=81/5000<3/80,
```

so the inherited finite-chart geometry remains valid.

## Promotion rule

Promotion requires eight production units, eight fresh replay units, exact
parsed-row equality, exact 720-cell adjacency, current dependency hashes,
one source head, and exact seams at lambda 2 and 18/5.  A single nonpositive
lower endpoint rejects the frozen route.
