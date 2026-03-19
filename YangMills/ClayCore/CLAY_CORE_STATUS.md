# Clay Core — BalabanRG Status (v1.0.4-alpha, 2026-03-19)

**~120 files · 0 errors · 0 analytic sorrys**

## The full finite geometry now reaches the high-level consumer chain.

## Three parallel paths — all green

### Path A — Skeleton baseline (v0.8.x)
0 analytic sorrys. Untouched. Stable anchor.

### Path B — Simplified bridge hierarchy (v0.9.x–v1.0.x)
BalabanLatticeSite d k = Fin(2^k) × Fin d (one coordinate)
- Full chain: 15A–15E, 11F–11H, 10B, CauchyDecayViaBridge ✅
- 6-path API in CauchyDecayFromAF ✅

### Path C — Full geometry bridge hierarchy (v1.0.3–v1.0.4) ✅
BalabanFiniteSite d k = Fin d → Fin(2^k) — full (ℤ/2^k ℤ)^d
```
BalabanFiniteLattice              — BalabanFiniteSite d k
LatticeSiteAdapterFull            — toBalabanFiniteSite: all d coordinates
PolymerGeometricReadoutFull       — ActivityFieldBridgeFull
PolymerCanonicalSiteFull          — canonicalGeometricBridgeFull
RGViaBridgeFull                   — RGViaBridgeControlFull (Core + Named bounds)
  ├── RGViaBridgeControlFullCore  — zero_field proved (0 sorrys)
  ├── FullLargeFieldSuppressionBound — P80-style (formal debt)
  └── FullCauchySummabilityBound  — P81-style (formal debt)
RGBridgeCompatibilityFull         — wrappers from RGViaBridgeControlFull
RGSkeletonViaBridgeFull           — skeleton-style facade
CauchyDecayViaBridgeFull          — FIRST HIGH-LEVEL CONSUMER (full geometry) ✅
```

## v1.0.4-alpha Key Milestones

| Milestone | Status |
|---|---|
| Full (ℤ/2^k ℤ)^d geometry | ✅ v1.0.3 |
| Full canonical bridge | ✅ v1.0.3 |
| RGViaBridgeControlFull (core proved) | ✅ v1.0.4 |
| Named analytic bounds (P80/P81 full) | ✅ structure (content deferred) |
| Full bridge consumer chain | ✅ v1.0.4 |
| CauchyDecayViaBridgeFull | ✅ v1.0.4 |

## Formal debt

| Gap | Location | Target |
|---|---|---|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow | P91 A.2 §3 |
| `RGBlockingMap` physical | BalabanBlockingMap | P78 |
| `FullLargeFieldSuppressionBound` proof | RGViaBridgeFull | P78/P80 |
| `FullCauchySummabilityBound` proof | RGViaBridgeFull | P81/P82 |
| Full path → CauchyDecayFromAF alias | v1.0.5 | |

## Next: v1.0.5-alpha
Start discharging formal debt:
1. Prove `FullLargeFieldSuppressionBound` for zero-field skeleton
2. Or: connect physical P80 estimate to full path
3. Add `..._via_canonical_full_bridge` alias to CauchyDecayFromAF
