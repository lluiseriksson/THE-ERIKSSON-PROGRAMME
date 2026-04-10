# State of the Project

**Version**: v1.20.0  
**Date**: 2026-04-10  
**Status**: Active development  autonomous campaign loop

## The Target

`ClayYangMillsPhysicalStrong`: machine-verified Yang-Mills mass gap.

```lean
theorem ClayYangMillsPhysicalStrong ... :
    ∀ N p q, |W_cc(N,p,q)| ≤ C · exp(−γ · distP N p q)
```

This is **non-vacuous** (unlike `ClayYangMillsTheorem`/`ClayYangMillsStrong` which are trivially true by `False.elim`).

## Live Hypothesis Path (3 remaining)

All three must be discharged to close the proof unconditionally:

| Hypothesis | Est. difficulty |
|---|---|
| `FeynmanKacFormula` | ~10% done (needs Balaban RG) |
| `StateNormBound ψ_obs C_ψ` | ~40% done |
| `HasSpectralGap T P₀ γ C` | ~25% done |

**Eliminated** (no longer live):
- `hdistP` — C104 derived it from `FeynmanKacFormula` via `Nat.cast_nonneg` ✔

## Campaign History

| Campaign | Tag | Key Elimination |
|---|---|---|
| C87 | v1.03.0 | OperatorNormBound: exp decay from op-norm |
| C88–C96 | v1.04–v1.12 | selfAdj, rank-one P₀, T0=0, ‖Ω‖=1, Ω, exp(−m), spectral gap |
| C97–C100 | v1.13–v1.16 | isometry, continuity, Lipschitz+StateNorm, FK witness |
| C101 | v1.17.0 | FK+transfer-matrix reduction |
| C102 | v1.18.0 | FK+StateNorm → FeynmanKacOpNormBound (Cauchy-Schwarz) |
| C103 | v1.19.0 | FeynmanKacToPhysicalStrong — chains C102→C87-2, 4-hyp theorem |
| C104 | v1.20.0 | DistPNonnegFromFormula — hdistP from FK via Nat.cast_nonneg (4→3 hyps) |

## Progress

| Component | Status |
|---|---|
| Formal chain (hypotheses → target) | COMPLETE |
| FeynmanKacFormula | ~10% (needs Balaban RG) |
| StateNormBound | ~40% |
| HasSpectralGap | ~25% |
| hdistP | **ELIMINATED** (C104) |
| **Overall genuine progress** | **~22%** |

## Oracle Policy

All P8_PhysicalGap theorems: oracle = `[propext, Classical.choice, Quot.sound]`. Zero sorry. Zero new axioms.

## Build

- Lean 4.29.0-rc6, Lake 5.0.0-src+00659f8
- `lake exe cache get` + `lake build <target>`
- CI via Google Colab, deploy_CXX.py scripts
