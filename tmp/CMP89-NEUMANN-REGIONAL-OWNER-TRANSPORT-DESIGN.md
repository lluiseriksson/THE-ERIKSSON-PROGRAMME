# CMP89 regional Green: scale/owner transport after (2.42)

Status: algebraic transport cold-sealed at source
`b9561132d1eaa2e55d4638bf42f1632effd64d68`; physical owner geometry still
design-only.  Ledger Addendum 974 and its locally verified archive are seal
authority, not this note.

## Input already constructed

The regional consumer at source checkpoint `466b9de31df1fd65ec86092908746a250edb5b4b`
rewrites the literal regional kernel by the named CMP89 (2.42)
representation certificate and obtains the exact bound

```text
2^4 * B0(a,rho)
  * product_mu (2 / (1 - exp (-(rho/L^j) * period_mu)))
  * exp (-(rho/L^j) * l1(x-n)).
```

The representation certificate remains a named source input.  This design
does not construct it.

## Next finite algebraic brick

Let `ell = L^j`.  The next theorem may consume only the following two visible
geometric facts:

1. `ell <= period_mu` for every coordinate;
2. `ell * ownerDist <= l1(x-n) + boundary`.

It must derive, without a rectangle-cardinality factor,

```text
norm (regionalGreen x n) <=
  2^4 * B0(a,rho)
    * (2 / (1 - exp (-rho)))^4
    * exp ((rho/ell) * boundary)
    * exp (-rho * ownerDist).
```

The proof has two independent gates:

- the period floor gives
  `exp (-(rho/ell)*period_mu) <= exp (-rho)` coordinatewise;
- the metric bridge gives
  `exp (-(rho/ell)*l1) <= exp ((rho/ell)*boundary) * exp (-rho*ownerDist)`.

Both uses require the positivity of `ell` and `rho`; the equality
`(rho/ell)*ell = rho` must be explicit rather than left to normalization.

## Physical dictionary still open

The algebraic brick may not introduce an arbitrary `ownerOf` map.  A later
source-facing producer must construct from the actual CMP89 rectangle and
CMP99 localization geometry:

- the rectangle side/period floor at `ell = L^j`;
- the owner index and its metric;
- the fine-to-owner bridge and its boundary payment;
- a depth-uniform bound on `(rho/ell)*boundary`.

Until those facts are constructed for the literal regional carrier, this
brick is infrastructure only.  It does not produce uniform physical
`B0, delta0`, attain window 15, discharge rows 23--24, move `20/41`, or
instantiate `TermSource`.

## Planned physical endpoint after the geometry gate

The literal CMP99 localization scale is `ell = L^(depth+1)`.  Its sealed
fine-to-owner bridge pays the exact boundary `2*(ell-1)`.  The final physical
consumer must therefore prove, rather than hide in a constant,

```text
(rho/ell) * (2*(ell-1)) <= 2*rho.
```

After this single calculation, the owner-rate endpoint has the depth-free
amplitude

```text
2^4 * B0(a,rho)
  * (2/(1-exp(-rho)))^4
  * exp(2*rho)
```

and owner rate `rho`.  The side/period floor and the rectangle fit into the
literal CMP99 carrier remain source-facing dictionary facts.  In particular,
the endpoint may not infer them from positivity of the side vector or replace
the varying rectangle by an arbitrary owner map.
