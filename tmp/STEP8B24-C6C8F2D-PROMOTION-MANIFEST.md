# C6c.8f2d retained exact read carrier promotion manifest

Status: **PRE-VALIDATION scratch only**.  No `.olean`, focal build or axiom
oracle exists for either module.

## Intended tracked paths

1. `YangMills/RG/BalabanCMP99SourceRetainedExactReadCarrier.lean`
2. `YangMills/RG/BalabanCMP99SourceRetainedExactReadCarrierAudit.lean`

## Source objects

- proof-carrying recursion: `CMP99SourceActiveRegionChain`;
- current-step carrier:
  `cmp99SourceTransportedAverageFineReadBonds`;
- tail pullback:
  `cmp99SourceUbarFineReadBondsOfCoarseBonds` applied to the recursively
  generated tail carrier.

## Acceptance boundary

The successor carrier is definitionally

```text
averageFineReadBonds(Omega)
  union UbarFineReadBondsOfCoarseBonds(tail.retainedFineReadBonds).
```

Agreement on it derives the current transported-average operator equality and
each raw Ubar equality requested by the tail.  The module does **not** assert
equality or locality of the complete global `nextBackground`.

The remaining f2 endpoint is to lift the raw Ubar equality to equality of the
literal direct-budget `SUN` blocks on the selected tail bonds and then perform
the induction on the generated retained `Qprime`.

## Audit queue

Seven readouts, exactly those in the companion audit file.  Expected allowed
axiom set is the standard project subset; no claim is made before sanctioned
elaboration and oracle output.
