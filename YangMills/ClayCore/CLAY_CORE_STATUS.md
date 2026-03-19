# Clay Core — BalabanRG Status (v1.0.3-alpha, 2026-03-19)

**~110 files · 0 errors · 0 analytic sorrys**

## Architecture: Dual Geometry + Canonical Bridge

### Path A — Skeleton baseline (v0.8.x)
0 analytic sorrys. Untouched. Stable anchor.

### Path B — Simplified bridge hierarchy (v0.9.x–v1.0.x)
BalabanLatticeSite d k = Fin(2^k) × Fin d

### Path C — Full geometry bridge hierarchy (v1.0.3-alpha) ✅
BalabanFiniteSite d k = Fin d → Fin(2^k) — full (ℤ/2^k ℤ)^d
```
BalabanFiniteLattice         — BalabanFiniteCoord k, BalabanFiniteSite d k
LatticeSiteAdapterFull       — toBalabanFiniteSite: LatticeSite→BalabanFiniteSite
                               coordinate-wise: all d coordinates
PolymerGeometricReadoutFull  — ActivityFieldBridgeFull (field on BalabanFiniteSite)
                               finiteReadoutFieldFull: ∑ K(p) at BalabanFiniteSite
                               singletonFiniteReadoutFieldFull_at_siteOf: key identity
PolymerCanonicalSiteFull     — canonicalGeometricBridgeFull ← polymer geometry ✅
                               canonicalBridgeFull_field_at_site: K(p₀) (0 sorrys)
                               canonicalBridgeFull_nonzero: K(p₀)≠0→field≠0
                               canonicalBridgeFull_consistent_with_polymer: Touches∧field
```

## v1.0.3-alpha Key Milestones

1. **Full lattice geometry**: `BalabanFiniteSite d k = Fin d → Fin(2^k)` — faithful (ℤ/2^k ℤ)^d
2. **Full adapter**: `toBalabanFiniteSite` — all d coordinates projected
3. **Full canonical bridge**: `canonicalGeometricBridgeFull` on full geometry
4. **Consistency**: `Polymer.Touches p₀ (canonicalSiteOf p₀)` + field = K(p₀)

## Full bridge hierarchy

| Bridge | Geometry | Determined by |
|---|---|---|
| `concreteActivityFieldBridge` | simplified | zero (stable anchor) |
| `singletonBridge` | simplified | fixed p₀, x₀ |
| `canonicalGeometricBridge` | simplified | `Classical.choose X.nonEmpty` |
| `canonicalGeometricBridgeFull` | **full** | `Classical.choose X.nonEmpty` ✅ |

## CauchyDecayFromAF — 6-path API
All paths green. Full-geometry path pending (v1.0.4).

## Formal debt

| Gap | Location | Target |
|---|---|---|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow | P91 A.2 §3 |
| `RGBlockingMap` physical | BalabanBlockingMap | P78 |
| Full bridge → RGViaBridgeControl | future | v1.0.4 |
| Skeleton→Bridge migration | P80/P81 | v1.0.x |

## Next: v1.0.4-alpha
1. `RGViaBridgeControlFull`: unify P80+P81 for ActivityFieldBridgeFull
2. High-level alias `cauchy_decay_via_canonical_geometric_bridge_full`
3. Full skeleton integration
