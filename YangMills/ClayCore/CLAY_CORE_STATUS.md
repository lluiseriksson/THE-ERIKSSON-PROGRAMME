# Clay Core — BalabanRG Status (v1.0.6-alpha, 2026-03-20)

**~130 files · 0 errors · 0 analytic sorrys**

## Key milestone: singleton polymer discharge

P80 and P81 are now fully discharged for the singleton bridge {p₀}.
Progression: ∅ (v1.0.5) → {p₀} (v1.0.6) → general (future induction).

## Three parallel paths — all green

### Path A — Skeleton baseline (v0.8.x)
0 analytic sorrys. Stable anchor.

### Path B — Simplified bridge hierarchy (v0.9.x–v1.0.x)
BalabanLatticeSite d k = Fin(2^k) × Fin d

### Path C — Full geometry bridge hierarchy (v1.0.3–v1.0.6) ✅
BalabanFiniteSite d k = Fin d → Fin(2^k)
```
BalabanFiniteLattice
LatticeSiteAdapterFull          — coordinate-wise projection
PolymerGeometricReadoutFull     — ActivityFieldBridgeFull
PolymerCanonicalSiteFull        — canonical bridge from polymer geometry
  canonicalBridgeFull_field_at_site    : field = K(p₀) at canonical site
  canonicalBridgeFull_field_zero_offsite: field = 0 elsewhere (0 sorrys)
RGViaBridgeFull                 — 3-layer control structure
RGBridgeCompatibilityFull
RGSkeletonViaBridgeFull
CauchyDecayViaBridgeFull        — high-level consumer ✅

FullLargeFieldSuppressionSkeleton — ∅ polys discharged (v1.0.5)
  emptyCanonicalGeometricBridgeControlFull: P80+P81 for ∅

FullLargeFieldSuppressionSingleton — {p₀} discharged (v1.0.6) ✅
  canonicalBridgeFull_field_zero_offsite: off-site = 0 (explicit filter)
  SingletonFullLargeFieldBound: named P80 hypothesis
  singleton_full_large_field_suppression: by_cases (0 sorrys) ✅
  SingletonFullCauchyBound: named P81 hypothesis
  singleton_full_cauchy_summability: by_cases (0 sorrys) ✅
  singletonCanonicalGeometricBridgeControlFull: first non-trivial control ✅
```

### CauchyDecayFromAF — 7-path API

## Formal debt

| Gap | Location | Target |
|---|---|---|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow | P91 A.2 §3 |
| `RGBlockingMap` physical | BalabanBlockingMap | P78 |
| `SingletonFullLargeFieldBound` proof | P78/P80 content | v1.0.7+ |
| `SingletonFullCauchyBound` proof | P81/P82 content | v1.0.7+ |
| General polys inductive discharge | finset induction | v1.0.7+ |

## Next: v1.0.7-alpha
Option A: discharge `SingletonFullLargeFieldBound` from ActivityNorm
Option B: inductive step ∅→{p₀}→polys∪{p₀}

- Finite-support full bridge consumer chain reached
- `CauchyDecayFromAF` extended with finite full alias


## v1.0.8-alpha
- Pointwise-to-singleton large-field bridge added
- Pointwise-to-singleton Cauchy bridge added
- Pointwise singleton full bridge reaches `CauchyDecayFromAF`


## v1.0.10-alpha
- First concrete `ActivityNorm` instance added: finite `L¹` norm on `ActivityFamily`
- `ActivityNormEvaluationBoundAt` discharged with constant `1` for the concrete `L¹` family
- `ActivityNormEvaluationCauchyBoundAt` discharged from the same concrete input
- Concrete `L¹` singleton path exposed at high level in `CauchyDecayFromAF`


## v1.0.11-alpha
- Concrete finite-support full bridge bounds discharged from the concrete `L¹` norm family
- Concrete packaged finite full control added via `finiteCanonicalGeometricBridgeControlFull_l1`
- High-level finite full `L¹` path exposed in `CauchyDecayFromAF`

v1.0.12-alpha
- Weighted finite L¹ ActivityNorm family introduced
- Native evaluation/Cauchy bounds discharged under 1 ≤ w
- Finite full bridge bounds discharged from weighted L¹
- Unit-weight specialization w ≡ 1 validates the weighted architecture against the previous concrete basepoint

## v1.0.13-alpha
- Abstract polymer weight interface introduced
- Native polymer-size weight `w(X)=|X|` instantiated through the interface
- Weighted evaluation and finite-full bridge machinery validated for `sizeWeight`
- `CauchyDecayFromAF` extended with the finite full size-weight alias


## v1.0.14-alpha
- Exponential polymer-size weight introduced: `w_a(X) = exp(a * |X|)`
- Abstract polymer-weight interface now instantiated with a KP-shaped weight
- Finite-full weighted bridge path validated for exponential size weights
- `CauchyDecayFromAF` extended with the exp-size-weight finite-full alias


## v1.0.15-alpha
- Structural lemmas added for the exponential polymer-size weight `w_a(X)=exp(a*|X|)`
- KP pointwise activity bounds rewritten through the exp-size-weight language
- Weighted smallness form `|K X| * w_a(X) ≤ a` available in native and scale-specialized versions

## v1.0.16-alpha
- Abstract KP weighted-activity interface introduced
- Weighted compatible-family budget interface added
- Weighted KP budgets now recover native `SmallActivityBudget` and `|Z - 1| ≤ B`
- Exponential polymer-size weight inserted as the first KP-side concrete instance
- Conservative exp-size-weight specialization closed through explicit `w ≥ 1`
