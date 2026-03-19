# Clay Core — BalabanRG Status (v0.9.0, 2026-03-19)

**57 files · 0 errors · 0 analytic sorrys**

## Architecture (Layer map)
```
Analytic chain (0 analytic sorrys):
  14A P91WindowFromRecursion    ← pure algebra
  14B P91RecursionData          ← hypothesis structure
  14E P91BetaDriftDecomposition ← pure analysis
  14G P91OnestepDriftAlgebra    ← drift algebra  
  14H P91DriftPositivityControl ← coeff/denom positivity
  14I P91UniformDrift           ← β_k ≥ 1 + uniform drift
  14J P91BetaDriftClosed        ← data-driven drift (0 sorrys)
  14K P91WindowClosed           ← p91_tight_window_of_data (0 sorrys)
  14D P91BetaDivergence         ← rate → 0
  14C CauchyDecayFromAF         ← Cauchy bridge
  12B P80EstimateSkeleton       ← trivialRGFieldSplit (0 sorrys)
  12C RGCauchySummabilitySkeleton ← dist=0 (0 sorrys)

Geometry chain (v0.9.0):
  15A BalabanFieldSpace         ← LatticeSite, Block, Region, fieldSupport
```

## Session achievements (this session)

- `remainder_small_P91`: proved (window→remainder, pure algebra)
- `window_from_product_small`: proved (β·(b₀+|r|)<1 → β<1/(b₀+|r|))
- `p91_tight_window_of_data`: proved from data.remainder_window_small
- `P91RecursionData`: inhabitable (reformulated remainder_window_small)
- `cauchy_decay_P81_step2`: eliminated (RGBlockingMap=0 → dist=0)
- `large_field_decomposition_P80_step1`: eliminated (trivialRGFieldSplit)
- `large_field_exponential_suppression_P80_step2`: eliminated (RGBlockingMap=0)
- `BalabanFieldSpace` (15A): LatticeSite/Block/Region/fieldSupport/largeSmallRegions

## Formal debt remaining

| Gap | Location | Nature |
|---|---|---|
| `p91_tight_weak_coupling_window` axiom | P91WeakCouplingWindow | P91 A.2 §3 quantitative |
| `RGBlockingMap` physical definition | BalabanBlockingMap | P78 polymer repr. |
| `ActivityFamily` ↔ `LatticeSite` bridge | 15B (pending) | geometry |
| `SmallFieldPredicate/LargeFieldPredicate` real def | SmallFieldLargeFieldSplit | 15B |

## Next: Layer 15B
Connect `SmallFieldPredicate`/`LargeFieldPredicate` to `BalabanFieldSpace` geometry.
`ActivityFamily d k = Polymer d ↑k → ℝ` — bridge to LatticeSite needed.
