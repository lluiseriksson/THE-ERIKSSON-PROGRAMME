# F3 Base-Zone Origin Certificate Code Injection Interface v2.228

Task: `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-INTERFACE-001`
Status: `DONE_INTERFACE_AND_BRIDGE_LANDED`
Timestamp: `2026-04-28T04:05:00Z`

## Lean Additions

- Added `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData`.
- Added `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`.
- Added `physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296`.

The new interface is strictly upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296`.  It
exposes only a selector-independent residual-value code into `Fin 1296` on the
whole residual subtype plus selected-admissible equality-reflection for values
carrying `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
evidence from essential parents.

## Bridge

The bridge target is:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

The bridge packages the code-injection data into the v2.226 source carrier by
using:

- `baseZoneCoordinateSpace residual := Fin 1296`;
- trivial `Unit` origin certificates and certificate sources;
- `True` validity and realization predicates;
- the supplied residual-value code as the coordinate;
- identity encoding into `Fin 1296`;
- the supplied selected-admissible equality-reflection field for
  `selectorAdmissible_certificate_injective`.

This is an erasure/repackaging bridge.  It does not prove the code-injection
theorem itself and does not close F3-COUNT.

## Guardrails

This interface and bridge do not use selected-image cardinality, bounded menu
cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes,
local-neighbor codes, local-displacement codes, parent-relative
`terminalNeighborCode` equality, deleted-X shortcuts, or the v2.161 cycle.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- New `#print axioms` traces for the new data carrier, proposition, and bridge
  are no larger than `[propext, Classical.choice, Quot.sound]`.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Blocker

The remaining proof lane is to prove:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

or reduce it to the next exact no-closure blocker.
