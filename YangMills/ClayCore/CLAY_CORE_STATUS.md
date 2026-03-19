# Clay Core — BalabanRG Status (v1.0.0-alpha, 2026-03-19)

**~80 files · 0 errors · 0 analytic sorrys**

## Architecture: Dual Path

### Path A — Skeleton baseline (v0.8.x, stable)
```
BalabanBlockingMap → SmallFieldLargeFieldSplit →
P80EstimateSkeleton → RGCauchySummabilitySkeleton → CauchyDecayFromAF
P91 chain (14A–14K) → CauchyDecayFromAF
```
Status: **0 analytic sorrys**. Will remain untouched until Path B is promoted.

### Path B — Geometry via bridge (v0.9.x, operational)
```
15A  BalabanFieldSpace           — lattice geometry
15B  SmallFieldLargeFieldSplit   — fieldThreshold=exp(-β/2), predicates
15C  BalabanFieldDecomposition   — φ=φ_small+φ_large
15D  ActivityFieldBridge         — abstract ActivityFamily→Field interface
15E  ActivityFieldSplitSelection — selectFieldSplitViaBridge (if/else real)
15F  ActivityFieldSuppression    — suppression_bound_small/large
15G  P80EstimateViaBridge        — p80_via_bridge_unified (0 sorrys)
15H  P81EstimateViaBridge        — p81_via_bridge_unified (0 sorrys)
11F  RGViaBridge                 — RGViaBridgeControl: unified P80+P81
11G  RGBridgeCompatibility       — re-expresses skeleton API via control
11H  RGSkeletonViaBridge         — facade: skeleton signature, bridge logic
10B  CauchyDecayViaBridge        — FIRST HIGH-LEVEL CONSUMER MIGRATED ✅
```
Status: **0 sorrys end-to-end**. `bridge_path_recovers_skeleton`: consistency proved.

## v1.0.0-alpha Criteria — ALL MET ✅

| Criterion | Status |
|---|---|
| Skeleton baseline green | ✅ |
| Bridge path green 15A–10B | ✅ |
| Unified API (RGViaBridgeControl) | ✅ |
| First high-level consumer migrated | ✅ CauchyDecayViaBridge |
| Consistency proof | ✅ bridge_path_recovers_skeleton |

## Formal debt

| Gap | Location | Target |
|---|---|---|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow | P91 A.2 §3 |
| `RGBlockingMap` physical | BalabanBlockingMap | P78 |
| `fieldOfActivity` concrete impl | ConcreteActivityFieldBridge | v1.0.1 |
| Skeleton → Bridge migration | P80/P81 | v1.0.x |

## Next: v1.0.1-alpha
1. Add `..._via_bridge` aliases in CauchyDecayFromAF (public API)
2. ConcreteActivityFieldBridge: first non-trivial fieldOfActivity
3. Begin P80EstimateSkeleton → RGViaBridgeControl migration
