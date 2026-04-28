# F3 Base-Zone Origin Certificate Code Injection Scope

Task: `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-SCOPE-001`
Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`
Timestamp: `2026-04-28T03:55:00Z`

## Proposed Upstream Theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296
```

## Why This Is Not A Restatement

`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296` asks for a whole v2.226 source carrier: certificate source, erasure to certificates, source validity, certificate realization, coordinate extraction, encoding into `Fin 1296`, and certificate-level selected-admissible injectivity.

The proposed upstream theorem isolates only the missing mathematical principle from the v2.227 no-closure attempt:

- a selector-independent residual-value code on the whole residual subtype;
- an encoding into `Fin 1296`;
- equality-reflection for selector-admissible residual values carrying `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from essential parents.

Once those are available, the remaining v2.226 certificate/source fields can be filled by a thin concrete carrier, without adding a new proof claim about the code.

## Suggested Data Shape

A future no-sorry Lean interface can use a carrier along these lines:

```lean
structure
  PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
    {L : Nat} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        Finset (ConcretePlaquette physicalClayDimension L)) where
  baseZoneOriginCertificateCode :
    forall residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q in residual} ->
        Fin 1296

  selectorAdmissible_code_injective :
    forall residual
      (a b : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      (exists p : {p : ConcretePlaquette physicalClayDimension L //
          p in essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) ->
      (exists p : {p : ConcretePlaquette physicalClayDimension L //
          p in essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) ->
      baseZoneOriginCertificateCode residual a =
        baseZoneOriginCertificateCode residual b ->
      a.1 = b.1
```

The theorem should reuse the same v2.121 bookkeeping residual-fiber hypotheses as the v2.226 source interface:

- `deleted`;
- `parentOf`;
- `essential`;
- safe-deletion/bookkeeping choice evidence;
- the image characterization of `essential residual`;
- `essential residual ⊆ residual`.

It should conclude:

```lean
Nonempty
  (PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
    (L := L) essential)
```

for each bookkeeping configuration.

## Expected Bridge

Assuming the code-injection theorem, the bridge into `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296` can instantiate:

- `baseZoneCoordinateSpace residual := Fin 1296`;
- `baseZoneOriginCertificate residual q := Unit`;
- `baseZoneOriginCertificateSource residual q := Unit`;
- source validity and certificate realization as `True`;
- `baseZoneCoordinateOfCertificate residual q _ := baseZoneOriginCertificateCode residual q`;
- `baseZoneCoordinateIntoFin1296 residual c := c`;
- `selectorAdmissible_certificate_injective` by applying `selectorAdmissible_code_injective`.

This bridge would be an erasure/repackaging bridge only. The proof content remains entirely in the code-injection theorem.

## Non-Circular Proof Routes To Investigate

### Route A: Structural residual base-zone coordinate

Construct a residual-local bookkeeping/base-zone coordinate for every residual member and prove that selector-admissible members have distinct coordinates. This is the preferred route if a genuine residual-value coordinate exists in the v2.121 bookkeeping data.

### Route B: Essential-parent certificate separation

Use the image characterization of `essential residual` to derive a selector-independent certificate for residual values that can occur as terminal-neighbor selector outputs from essential parents. The code must be defined on the whole residual subtype before admissibility is supplied; admissibility may only be used in the equality-reflection lemma.

### Route C: New structural invariant

Introduce an upstream invariant saying that the v2.121 bookkeeping residual fibers carry a base-zone certificate map into `Fin 1296` with selected-admissible equality-reflection. This route is acceptable only if the invariant is independent of selected-image cardinality and bounded menus.

## Rejected Routes

This scope does not authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- root-shell codes as residual-subtype bookkeeping/base-zone injectivity;
- local-neighbor codes as residual-subtype bookkeeping/base-zone injectivity;
- local-displacement codes as residual-subtype bookkeeping/base-zone injectivity;
- parent-relative `terminalNeighborCode` equality;
- deleted-X shortcut, i.e. treating deleted `X` as a residual terminal neighbor for `residual = X.erase (deleted X)`;
- the v2.161 cycle, including the v2.161 selector-image cycle.

## Validation

- This dashboard note exists.
- It names the exact bridge into `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296`.
- No Lean file was edited; no `lake build` was required for this dashboard-only scope.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric, planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-INTERFACE-001
```

Add the no-sorry Lean Prop/interface and, only if it builds without `sorry`, the bridge:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296
```
