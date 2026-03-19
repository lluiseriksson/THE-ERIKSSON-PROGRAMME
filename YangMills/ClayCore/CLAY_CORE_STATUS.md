# Clay Core — BalabanRG Status (v1.0.5-alpha, 2026-03-19)

**~125 files · 0 errors · 0 analytic sorrys**

## Key milestone: first filled RGViaBridgeControlFull

The full-geometry control package is no longer only hypothetical:
it is fully discharged for the empty-polymer bridge. 0 sorrys.

## Three parallel paths — all green

### Path A — Skeleton baseline (v0.8.x)
0 analytic sorrys. Stable anchor.

### Path B — Simplified bridge hierarchy (v0.9.x–v1.0.x)
BalabanLatticeSite d k = Fin(2^k) × Fin d

### Path C — Full geometry bridge hierarchy (v1.0.3–v1.0.5) ✅
BalabanFiniteSite d k = Fin d → Fin(2^k)
```
BalabanFiniteLattice
LatticeSiteAdapterFull        — coordinate-wise projection
PolymerGeometricReadoutFull   — ActivityFieldBridgeFull
PolymerCanonicalSiteFull      — canonical bridge from polymer geometry
RGViaBridgeFull               — 3-layer: Core + Named bounds + Package
RGBridgeCompatibilityFull
RGSkeletonViaBridgeFull
CauchyDecayViaBridgeFull      — high-level consumer ✅
FullLargeFieldSuppressionSkeleton — DISCHARGED for ∅ ✅
  empty_polys_full_bridge_field_zero  : field=0 for ∅
  empty_full_large_field_suppression  : P80 bound discharged
  empty_full_cauchy_summability       : P81 bound discharged
  emptyCanonicalGeometricBridgeControlFull : first filled RGViaBridgeControlFull ✅
```

### CauchyDecayFromAF — 7-path API
```
baseline / abstract-bridge / concrete / singleton / geometric /
canonical-geometric / canonical-geometric-full (← new)
```

## Formal debt

| Gap | Location | Target |
|---|---|---|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow | P91 A.2 §3 |
| `RGBlockingMap` physical | BalabanBlockingMap | P78 |
| `FullLargeFieldSuppressionBound` for `{p₀}` | v1.0.6 | singleton |
| `FullCauchySummabilityBound` for `{p₀}` | v1.0.6 | singleton |
| General polys inductive discharge | v1.0.7+ | inductive |

## Next: v1.0.6-alpha
1. `singleton_full_large_field_suppression`
2. `singleton_full_cauchy_summability`
3. `singletonCanonicalGeometricBridgeControlFull`
Then inductive step: ∅ → {p₀} → finite union.
