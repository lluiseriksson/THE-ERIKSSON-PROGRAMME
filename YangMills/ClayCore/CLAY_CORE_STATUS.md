# Clay Core — BalabanRG Status (v0.9.11, 2026-03-19)

**~75 files · 0 errors · 0 analytic sorrys**

## Geometry chain (v0.9.x) — complete
```
15A  BalabanFieldSpace
       BalabanLatticeSite = Fin(2^k) × Fin d
       Block, Region, balabanFieldSupport
       balabanLargeFieldRegion, balabanSmallFieldRegion
       balabanLargeSmallPartition, balabanLargeSmallDisjoint

15B  SmallFieldLargeFieldSplit (Layer 11D extended)
       fieldThreshold β = exp(-β/2)  ← physical
       SmallFieldPredicateField, LargeFieldPredicateField
       smallField_iff, small_or_large_field
       RGFieldSplitOnField (parallel structure)
       trivialRGFieldSplitOnField, largeOnlyRGFieldSplitOnField
       selectFieldSplit, largeFieldNorm (.card)

15C  BalabanFieldDecomposition
       smallFieldProjection, largeFieldProjection
       small_add_large_eq: φ = φ_small + φ_large  (0 sorrys)
       support inclusion and disjointness lemmas
       eq_self_of_small, eq_zero_of_small

15D  ActivityFieldBridge
       ActivityFieldBridge: fieldOfActivity + zero_field
       inducedFieldSupport, inducedLargeFieldRegion
       SmallFieldPredViaBridge, LargeFieldPredViaBridge
       small_or_large_via_bridge, zero_activity_small
       not_small_of_large_via_bridge

15E  ActivityFieldSplitSelection  (above 15B+15D, no cycle)
       selectFieldSplitViaBridge: if Small → trivial else largeOnly
       Case lemmas: _of_small, _of_large (0 sorrys)
       Projection pillars: ×4 (0 sorrys)
       zero_activity_uses_trivial

15F  ActivityFieldSuppression
       selected_split_cases: binary OR (0 sorrys)
       largeField_part_vanishes_on_small (0 sorrys)
       smallField_part_vanishes_on_large (0 sorrys)
       suppression_bound_small/large: dist=0 (0 sorrys)

15G  P80EstimateViaBridge
       large_field_decomposition_via_bridge_small
       p80_via_bridge_unified: ≤ exp(-β)·dist(K,0) (0 sorrys)

15H  P81EstimateViaBridge
       cauchy_decay_via_bridge_small/small'/large (0 sorrys)
       p81_via_bridge_unified: ≤ C·dist(K₁,K₂) (0 sorrys)

11F  RGViaBridge  ← UNIFIED API
       RGViaBridgeControl: large_field_bound + cauchy_bound
       rg_large_field_suppression_via_bridge (P80 wrapper)
       rg_cauchy_decay_via_bridge (P81 wrapper)
       rg_control_via_bridge: any bridge → RGViaBridgeControl
       trivialBridgeControl: inhabited
       Extractor lemmas: _large_field_bound, _cauchy_bound
```

## Analytic chain (v0.8.x) — ALL 0 analytic sorrys
```
P91 drift/divergence/rate chain: 0 sorrys end-to-end
P80 §4.1/4.2: 0 sorrys (trivialRGFieldSplit)
P81 §3: 0 sorrys (RGBlockingMap=0)
```

## DAG summary
```
BalabanFieldSpace (15A)
    └─ SmallFieldLargeFieldSplit (15B)
         └─ ActivityFieldBridge (15D)
         └─ BalabanFieldDecomposition (15C)
         └─ ActivityFieldSplitSelection (15E)  ← above 15B+15D
              └─ ActivityFieldSuppression (15F)
                   └─ P80EstimateViaBridge (15G)
                   └─ P81EstimateViaBridge (15H)
                        └─ RGViaBridge (11F)  ← unified API

Analytic baseline (v0.8.x):
  BalabanBlockingMap → SmallFieldLargeFieldSplit →
  P80EstimateSkeleton → RGCauchySummabilitySkeleton → CauchyDecayFromAF
  P91 chain (14A–14K) → P91BetaDriftClosed → P91BetaDivergence → CauchyDecayFromAF
```

## Formal debt

| Gap | Location | Note |
|---|---|---|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow | P91 A.2 §3 axiom |
| `RGBlockingMap` physical def | BalabanBlockingMap | P78, deferred |
| `ActivityFieldBridge.fieldOfActivity` concrete | future 15I | Polymer→Site |
| Skeleton → ViaBridge migration | P80/P81 Skeletons | v1.0 |

## Next: v0.9.12 or v1.0.0-alpha
Options:
1. Migrate P80EstimateSkeleton to consume RGViaBridgeControl
2. Introduce ActivityFieldBridge concrete implementation
3. Begin v1.0.0-alpha: activate RGBlockingMap from P78
