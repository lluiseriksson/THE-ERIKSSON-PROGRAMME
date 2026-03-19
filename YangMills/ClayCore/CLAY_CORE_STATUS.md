# Clay Core — BalabanRG Status (v1.0.1-alpha, 2026-03-19)

**~90 files · 0 errors · 0 analytic sorrys**

## Architecture: Dual Path + Non-trivial Bridge

### Path A — Skeleton baseline (v0.8.x)
```
BalabanBlockingMap → SmallFieldLargeFieldSplit →
P80EstimateSkeleton → RGCauchySummabilitySkeleton → CauchyDecayFromAF
P91 chain (14A–14K) → CauchyDecayFromAF
```
Status: **0 analytic sorrys. Untouched. Stable.**

### Path B — Bridge path (v0.9.x–v1.0.x, operational)
```
15A  BalabanFieldSpace            — lattice geometry, Fin(2^k)×Fin d
15B  SmallFieldLargeFieldSplit    — fieldThreshold=exp(-β/2), predicates
15C  BalabanFieldDecomposition    — φ=φ_small+φ_large
15D  ActivityFieldBridge          — abstract ActivityFamily→Field interface
15E  ActivityFieldSplitSelection  — selectFieldSplitViaBridge (real if/else)
15F  ActivityFieldSuppression     — suppression_bound_small/large
15G  P80EstimateViaBridge         — p80_via_bridge_unified (0 sorrys)
15H  P81EstimateViaBridge         — p81_via_bridge_unified (0 sorrys)
11F  RGViaBridge                  — RGViaBridgeControl: unified P80+P81
11G  RGBridgeCompatibility        — compatibility wrappers
11H  RGSkeletonViaBridge          — facade layer
10B  CauchyDecayViaBridge         — first high-level consumer (v1.0.0)
```

### Concrete bridge hierarchy (v1.0.x)
```
ConcreteActivityFieldBridge      — concreteActivityFieldBridge (zero readout, stable)
                                   concreteBridgeControl

PolymerSiteReadout               — abstract readout interface (Phase 1)
  PolymerSiteReadout structure   — readoutField + zero_field
  bridgeFromReadout               — readout → ActivityFieldBridge
  trivialPolymerSiteReadout       — zero readout
  rgControlFromReadout            — readout → RGViaBridgeControl

FinitePolymerReadout             — finite support readout (Phase 2+3)
  FinitePolymerReadout structure — polys: Finset + siteOf
  finiteReadoutField             — ∑ K(p) at site (non-trivial!) ✅
  emptyFinitePolymerReadout      — ∅ support
  singletonFinitePolymerReadout  — {p₀} → x₀ ← FIRST NON-TRIVIAL BRIDGE
  singletonBridge                — ActivityFieldBridge with K(p₀)≠0 possible ✅
  singletonBridgeControl         — RGViaBridgeControl from singleton
  singletonBridge_nonzero_of_activity_nonzero  — K(p₀)≠0 → field≠0 ✅
```

### CauchyDecayFromAF — triple API
```
cauchy_decay_from_p91_data               — baseline (always)
cauchy_decay_from_p91_data_via_bridge    — via abstract bridge
cauchy_decay_from_p91_data_via_concrete_bridge — via zero concrete bridge
cauchy_decay_from_p91_data_via_singleton_bridge — via non-trivial bridge ✅
```

## v1.0.1-alpha Milestones — ALL MET ✅

| Milestone | Status |
|---|---|
| Skeleton baseline green | ✅ |
| Bridge path 15A–10B green | ✅ |
| CauchyDecayFromAF: dual path | ✅ v1.0.1 Session 1 |
| ConcreteActivityFieldBridge: named instance | ✅ v1.0.1 Session 2 |
| PolymerSiteReadout: abstract Phase 1 | ✅ v1.0.1 Session 3 |
| FinitePolymerReadout: finite sum Phase 2 | ✅ v1.0.1 Phase 2 |
| singletonBridge: first non-trivial bridge | ✅ v1.0.1 Phase 3 |
| singletonBridge_nonzero: K(p₀)≠0→field≠0 | ✅ v1.0.1 Phase 3 |
| cauchy_decay_via_singleton_bridge: high-level | ✅ v1.0.1 Phase 3 |

## Formal debt

| Gap | Location | Target |
|---|---|---|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow | P91 A.2 §3 |
| `RGBlockingMap` physical | BalabanBlockingMap | P78 |
| Physical siteOf (Polymer→BalabanLatticeSite) | v1.0.2 | P78 geometry |
| Skeleton→Bridge full migration | P80/P81 Skeleton | v1.0.x |

## Next: v1.0.2-alpha
1. `PolymerGeometricReadout.lean`: physical siteOf from polymer structure
2. Non-artificial singleton: siteOf from polymer bounding box or center
3. First readoutField from real polymer geometry (P78 approach)
