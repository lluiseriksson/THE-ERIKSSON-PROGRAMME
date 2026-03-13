# THE ERIKSSON PROGRAMME — Master Roadmap

## Status: 2026-03-13

### Completed
- **Phase 1** (L0–L8.1): Full architectural chain, Clay terminal theorem
- **Phase 2** (P2.1–P2.5): Discharged hypothesis `∃ m_inf > 0` via Resultado A

### Remaining explicit hypotheses
1. `LatticeMassProfile.IsPositive` ← **Phase 3 target**
2. `HasContinuumMassGap` ← Phase 4 target

### Phase 3: Bałaban/RG Positivity (LatticeMassProfile.IsPositive)
Target: discharge `LatticeMassProfile.IsPositive` via abstract RG contraction.

**Mathlib v4.29 probe results for Phase 3:**
- `Subgroup.center` ✅
- `commutator`, `MulAut`, `Representation`, `ZMod` ✅
- `Matrix.perronFrobenius` ❌ (not available)
- `SimplicialComplex`, `Homology`, `chainComplex` ❌ (not available)
- `intersectionNumber`, `RootsOfUnity` ❌ (not available)

**Architecture decision:**
Phase 3 will NOT use algebraic topology or Perron-Frobenius directly.
Instead it will use abstract RG contraction predicates (same strategy as Phase 2).

Node plan:
- P3.1 CorrelationNorms.lean — connected-correlation decay witnesses
- P3.2 RGContraction.lean — one RG step improves decay predicate
- P3.3 MultiscaleDecay.lean — n-step iteration gives exponential decay
- P3.4 LatticeMassExtraction.lean — extract LatticeMassProfile.IsPositive
- P3.5 Phase3Assembly.lean — replace hypothesis in L8.1

### Phase 4: Continuum limit (HasContinuumMassGap)
Target: discharge `HasContinuumMassGap` via asymptotic freedom / UV RG.
Deferred until Phase 3 complete.

## Build stats
- Files: 29
- Theorems: ~230
- Sorrys: 0
- Jobs: 8183
