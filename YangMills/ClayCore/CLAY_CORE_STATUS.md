# Clay Core — BalabanRG Status (v0.9.6, 2026-03-19)

**63 files · 0 errors · 0 analytic sorrys**

## Geometry chain (v0.9.x) — Layer map
```
15A  BalabanFieldSpace          ← LatticeSite, Block, Region, fieldSupport
                                   largeFieldRegion, smallFieldRegion
                                   largeSmallPartition, largeSmallDisjoint

15B  SmallFieldLargeFieldSplit  ← fieldThreshold = exp(-β/2) [physical]
     (Layer 11D extended)          SmallFieldPredicateField, LargeFieldPredicateField
                                   small_or_large_field, smallField_iff
                                   selectFieldSplit (trivial)
                                   largeFieldNorm (cardinal)
                                   RGFieldSplitOnField (parallel structure)
                                   trivialRGFieldSplitOnField

15C  BalabanFieldDecomposition  ← smallFieldProjection, largeFieldProjection
                                   small_add_large_eq: φ = φ_small + φ_large ✅
                                   support lemmas: all 0 sorrys
                                   eq_self_of_small, eq_zero_of_small

15D  ActivityFieldBridge        ← ActivityFieldBridge structure
                                   inducedFieldSupport, inducedLargeFieldRegion
                                   SmallFieldPredViaBridge, LargeFieldPredViaBridge
                                   small_or_large_via_bridge, zero_activity_small

15E  ActivityFieldSplitSelection ← ABOVE 15B+15D (no cycle)
                                   selectFieldSplitViaBridge (trivial API)
                                   zero_activity_selects_small
                                   small_or_large_activity_via_bridge
```

## Analytic chain (v0.8.x) — All 0 analytic sorrys
```
P91 drift/divergence/rate: 0 sorrys end-to-end
P80 §4.1/4.2: 0 sorrys (trivialRGFieldSplit)
P81 §3: 0 sorrys (RGBlockingMap=0)
```

## Formal debt

| Gap | Location | Note |
|---|---|---|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow | P91 A.2 §3 |
| `RGBlockingMap` physical def | BalabanBlockingMap | P78, deferred |
| `ActivityFieldBridge.fieldOfActivity` concrete | future | Polymer→Site |
| `selectFieldSplitViaBridge` nontrivial | ActivityFieldSplitSelection | next |

## Next: v0.9.7
Make `selectFieldSplitViaBridge` nontrivial:
- if `SmallFieldPredViaBridge`: use trivial split
- if `LargeFieldPredViaBridge`: use a large-field suppression split
This is the first genuine physics-dependent RG selection.
