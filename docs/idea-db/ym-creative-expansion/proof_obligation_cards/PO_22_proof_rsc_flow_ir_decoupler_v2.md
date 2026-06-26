# Rsc/flow/IR decoupler

**Key:** `proof.flow.ir.bridge`
**Mission contract:** `OC_025_rsc_flow_ir_decoupler`
**Status:** `lean_linked / operational metadata only`

## Target shape

```text
polymer-local R bound -> scalar Rsc bridge -> coupling_recursion / ir_bound, with quantifiers not collapsed.
```

## Allowed source keys

- `crosswalk.flow-ir-asymptotic-freedom-route`
- `crosswalk.r-operation-polymer-local-route`
- `cmp119.r-term-bound.2.31`
- `proof.flow.ir.bridge`

## Minimal success

- separate scalar bridge target
- flow assumptions not used as activity proof
- IR remains theorem-fed/cited separately

## Reject if

- uses downstream H# or final Lemma 3 bound to prove an upstream field
- uses scalar Dimock architecture as a Yang-Mills theorem without a dictionary
- adds a monolithic raw-source package with the same live fields
- adds a downstream consumer while all old hypotheses remain
- rewrites polymer-local R bounds as M*r^k without bridge

## Boundary

This card routes an agent to a source-backed theorem target.  It is not source
evidence and must not be cited as a mathematical proof.
