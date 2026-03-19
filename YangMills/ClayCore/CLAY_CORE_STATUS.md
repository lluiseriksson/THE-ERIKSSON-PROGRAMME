# Clay Core — BalabanRG Status (v1.0.2-alpha, 2026-03-19)

**~100 files · 0 errors · 0 analytic sorrys**

## Architecture: Dual Path + Canonical Geometric Bridge

### Path A — Skeleton baseline (v0.8.x, stable)
0 analytic sorrys. Untouched.

### Path B — Bridge hierarchy (v0.9.x–v1.0.x)
```
B1  Abstract bridge        ActivityFieldBridge (interface)
B2  Concrete zero bridge   concreteActivityFieldBridge
B3  Singleton bridge       singletonBridge: K(p₀)≠0 → field≠0 ✅
B4  Geometric bridge       canonicalGeometricBridge ← polymer geometry ✅
```

### Geometry chain (v0.9.x–v1.0.2)
```
15A  BalabanFieldSpace          — BalabanLatticeSite = Fin(2^k)×Fin d
15B  SmallFieldLargeFieldSplit  — fieldThreshold=exp(-β/2)
15C  BalabanFieldDecomposition  — φ=φ_small+φ_large
15D  ActivityFieldBridge        — abstract interface
15E  ActivityFieldSplitSelection — selectFieldSplitViaBridge
15F  ActivityFieldSuppression   — suppression bounds
15G  P80EstimateViaBridge       — p80_via_bridge_unified
15H  P81EstimateViaBridge       — p81_via_bridge_unified
11F  RGViaBridge                — RGViaBridgeControl (unified)
11G  RGBridgeCompatibility      — compatibility layer
11H  RGSkeletonViaBridge        — facade
10B  CauchyDecayViaBridge       — first high-level consumer
     ConcreteActivityFieldBridge — zero bridge (stable)
     PolymerSiteReadout         — abstract readout
     FinitePolymerReadout       — Finset-based readout
       singletonFiniteReadoutField_at_siteOf: key identity ✅
     PolymerGeometricReadout    — PhysicalPolymerRepSite
     LatticeSiteAdapter         — toBalabanSite: LatticeSite→BalabanLatticeSite
     PolymerCanonicalSite       — canonical bridge from polymer geometry ✅
       canonicalSiteOf := Classical.choose X.nonEmpty
       canonicalBridge_field_at_site: field = K(p₀) at canonical site
       canonicalBridge_nonzero: K(p₀)≠0 → bridge field≠0
```

### CauchyDecayFromAF — full API (5 paths)
```
cauchy_decay_from_p91_data                    — baseline
cauchy_decay_from_p91_data_via_bridge         — abstract bridge
cauchy_decay_from_p91_data_via_concrete_bridge — zero concrete
cauchy_decay_from_p91_data_via_singleton_bridge — non-trivial
cauchy_decay_from_p91_data_via_geometric_bridge — physical (NeZero d)
cauchy_decay_from_p91_data_via_canonical_geometric_bridge — canonical ✅
```

## v1.0.2-alpha Key Milestone

**The bridge is now canonically determined by polymer geometry.**

`canonicalSiteOf X = Classical.choose X.nonEmpty ∈ X.sites`

This is the first bridge where the site assignment is derived from the polymer's
own geometric support — not an artificial fixed assignment.

## Formal debt

| Gap | Location | Target |
|---|---|---|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow | P91 A.2 §3 |
| `RGBlockingMap` physical | BalabanBlockingMap | P78 |
| `toBalabanSite` full geometry | LatticeSiteAdapter | v1.0.3 |
| Skeleton→Bridge migration | P80/P81 | v1.0.x |

## Next: v1.0.3-alpha
Refine `toBalabanSite`: current encoding uses only one coordinate.
Full geometry: `(ℤ/2^k ℤ)^d` not yet formalized.
