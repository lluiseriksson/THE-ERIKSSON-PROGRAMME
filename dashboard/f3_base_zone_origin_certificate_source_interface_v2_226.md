# F3 Base-Zone Origin Certificate Source Interface v2.226

Task: `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-SOURCE-INTERFACE-001`
Status: `DONE_INTERFACE_AND_BRIDGE_LANDED`
Timestamp: `2026-04-28T03:35:00Z`

## Lean additions

- Added `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData`.
- Added `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296`.
- Added `physicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296_of_baseZoneOriginCertificateSource1296`.

The new source data is intentionally upstream of the v2.224 realization/separation layer. It carries a selector-independent `baseZoneOriginCertificateSource`, an erasure map into `baseZoneOriginCertificate`, source validity, certificate realization, coordinate extraction from certificates, encoding into `Fin 1296`, and certificate-level selected-admissible injectivity for residual values carrying `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from essential parents.

The bridge erases source provenance into the v2.224 `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData` fields. It does not prove the source theorem itself and does not close F3-COUNT.

## Guardrails

This interface rejects the selected-image cardinality route, bounded menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell/local-neighbor/local-displacement codes as residual bookkeeping/base-zone injectivity, parent-relative `terminalNeighborCode` equality, deleted-X shortcuts, and the v2.161 circular selector-image chain.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed after the Lean edit.
- New `#print axioms` traces for `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData`, `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296`, and `physicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296_of_baseZoneOriginCertificateSource1296` are no larger than `[propext, Classical.choice, Quot.sound]`.
- `F3-COUNT` remains `CONDITIONAL_BRIDGE`; no percentage, ledger status, planner metric, README metric, or Clay-level claim moved.

## Next blocker

The remaining proof lane is to prove `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296` or reduce it to the next exact no-closure blocker by constructing concrete selector-independent origin/certificate source data.
