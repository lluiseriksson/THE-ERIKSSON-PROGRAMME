# State of the Project: Yang-Mills Formalization

**Version**: v1.18.0 (C102 complete) | **Date**: 2026-04-10

## Non-Vacuous Target

```lean
ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP
-- ∀ N p q, |W_cc(N,p,q)| ≤ C · exp(−γ · distP N p q)
```

`ClayYangMillsTheorem` and `ClayYangMillsStrong` are vacuously provable. Not the genuine goal.

## Live Path Hypotheses (4 remaining as of v1.18.0)

```
FeynmanKacFormula        -- FK transfer-matrix representation of W_cc        [OPEN]
StateNormBound           -- ‖ψ_obs N p‖ ≤ C_ψ                                   [OPEN]
HasSpectralGap T P₀ γ C  -- spectral gap of the transfer matrix              [OPEN]
hdistP                   -- ∀ N p q, 0 ≤ distP N p q                        [OPEN]
```

The formal chain is complete: these 4 → `ClayYangMillsPhysicalStrong`.

## Campaign History (P8_PhysicalGap, C87–C102)

| Campaign | Tag | Key Elimination |
|----------|-----|----------------|
| C87 | v1.03.0 | OperatorNormBound: exp decay from op-norm |
| C88–C96 | v1.04–v1.12 | selfAdj, rank-one P₀, TΩ=Ω, ‖Ω‖=1, Ω, exp(-m), spectral gap |
| C97–C100 | v1.13–v1.16 | isometry, continuity, Lipschitz→StateNorm, FK witness |
| C101 | v1.17.0 | FK→transfer-matrix reduction |
| C102 | v1.18.0 | FK+StateNorm → FeynmanKacOpNormBound (Cauchy-Schwarz) |

## Progress

| Component | Status |
|-----------|--------|
| Formal chain (hypotheses → target) | COMPLETE |
| FeynmanKacFormula | ~10% (needs Balaban RG) |
| StateNormBound | ~40% |
| HasSpectralGap | ~25% |
| hdistP | ~90% |
| **Overall genuine progress** | **~19%** |

## Oracle Policy

All P8_PhysicalGap theorems: oracle = `[propext, Classical.choice, Quot.sound]`. Zero sorry. Zero new axioms.

## Build

- Lean 4.29.0-rc6, Lake 5.0.0-src+00659f8
- `lake exe cache get` + `lake build <target>`
- CI via Google Colab, deploy_CXX.py scripts
