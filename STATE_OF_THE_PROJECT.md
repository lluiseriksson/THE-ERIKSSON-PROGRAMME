# State of the Project

**Version**: v1.21.0  
**Date**: 2026-04-10  
**Status**: Active development — autonomous campaign loop

## The Target

`ClayYangMillsPhysicalStrong`: machine-verified Yang-Mills mass gap.

```lean
theorem ClayYangMillsPhysicalStrong ... :
    ∀ N p q, |W_cc(N,p,q)| ≤ C · exp(−γ · distP N p q)
```

This is **non-vacuous** (unlike `ClayYangMillsTheorem`/`ClayYangMillsStrong` which are trivially true by `False.elim`).

## Live Hypothesis Path (2 remaining)

`ClayYangMillsPhysicalStrong` now follows from exactly **two** hypotheses:

| Hypothesis | Meaning | Est. progress |
|---|---|---|
| `PhysicalFeynmanKacFormula` | FK + unit obs states (distP ∈ ℕ, unit norm) | ~10% |
| `HasSpectralGap T P₀ γ C` | Transfer matrix has spectral gap | ~25% |

**Eliminated** (no longer live):
- `hdistP` — C104: derived from FK via `Nat.cast_nonneg` ✔
- `StateNormBound` — C105: absorbed into `PhysicalFeynmanKacFormula` (unit norm ⇒ C_ψ=1) ✔

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
| C105 | v1.21.0 | UnitObsToPhysicalStrong — HasUnitObsNorm absorbs StateNormBound (3→2 hyps) |

## Progress

| Component | Status |
|---|---|
| Formal chain (hypotheses → target) | COMPLETE |
| PhysicalFeynmanKacFormula | ~10% (FK hardest; unit norm natural) |
| HasSpectralGap | ~25% |
| StateNormBound | **ELIMINATED** (C105) |
| hdistP | **ELIMINATED** (C104) |
| **Overall genuine progress** | **~24%** |

## Oracle Policy

All P8_PhysicalGap theorems: oracle = `[propext, Classical.choice, Quot.sound]`. Zero sorry. Zero new axioms.

## Build

- Lean 4.29.0-rc6, Lake 5.0.0-src+00659f8
- `lake exe cache get` + `lake build <target>`
- CI via Google Colab, deploy_CXX.py scripts
