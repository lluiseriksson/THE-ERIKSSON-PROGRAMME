# F3 Base-Zone Origin Certificate Source Attempt v2.227

Task: `CODEX-F3-PROVE-BASE-ZONE-ORIGIN-CERTIFICATE-SOURCE-001`
Status: `DONE_NO_CLOSURE_CERTIFICATE_CODE_INJECTION_MISSING`
Timestamp: `2026-04-28T03:45:00Z`

## Target

Attempted target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

The v2.226 interface and bridge are available:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData
physicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296_of_baseZoneOriginCertificateSource1296
```

## Result

No Lean proof was added. The current Lean API still does not construct the selector-independent residual bookkeeping/base-zone certificate code injection needed by the v2.226 source data.

A non-circular construction can provide the source/erasure/validity/realization shell once a selector-independent code exists. The proof stops exactly at the field:

```lean
selectorAdmissible_certificate_injective
```

That field requires an encoding into `Fin 1296` whose equality reflects equality of selector-admissible residual values carrying `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from essential parents. Existing local codes do not supply this:

- root-shell codes only live in the root shell, not on arbitrary residual values;
- local-neighbor/local-displacement codes are parent- or edge-local, not residual-subtype bookkeeping/base-zone injectivity;
- `terminalNeighborCode` is selector-data-local and parent-relative;
- `finsetCodeOfCardLe`, selected-image cardinality, bounded menu cardinality, and empirical search are explicitly forbidden for this lane.

Using `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296` or the v2.226 interface itself as evidence would be circular and was not done.

## Exact no-closure blocker

The next upstream theorem should isolate the missing code-injection principle, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

Expected bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

Expected bridge idea:

1. assume a selector-independent residual-value code
   `∀ residual, {q // q ∈ residual} → Fin 1296`;
2. assume certificate-level selected-admissible injectivity for that code;
3. instantiate `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData` with a simple concrete certificate/source carrier over the whole residual subtype;
4. use the supplied code-injectivity theorem for `selectorAdmissible_certificate_injective`.

## Rejected routes

This attempt did not use selected-image cardinality, bounded menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell/local-neighbor/local-displacement codes as residual bookkeeping/base-zone injectivity, parent-relative `terminalNeighborCode` equality, deleted-X shortcuts, or the v2.161 selector-image cycle.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- No new Lean theorem was added in this attempt, so there is no new axiom trace beyond the v2.226 interface traces already recorded.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric, planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next task

```text
CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-SCOPE-001
```

Scope the upstream certificate-code injection theorem and its bridge into `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296`.
