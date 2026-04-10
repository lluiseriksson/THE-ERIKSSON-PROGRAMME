# The Eriksson Programme: Machine-Verified Yang-Mills Mass Gap

**v1.20.0** | Lean 4.29.0-rc6 / Mathlib4 | Autonomous campaign loop active

## What This Is

A long-term Lean 4 formalization project targeting the **Yang-Mills existence and mass gap** problem (one of the Clay Millennium Problems). The goal is to reach a fully machine-verified proof of `ClayYangMillsPhysicalStrong` with zero `sorry` and only standard axioms.

## The Non-Vacuous Target

```lean
theorem ClayYangMillsPhysicalStrong
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ) :
    ∃ C γ : ℝ, 0 < γ ∧ ∀ N p q,
      |wilsonConnectedCorr μ plaquetteEnergy β F N p q| ≤ C * Real.exp (-γ * distP N p q)
```

This is **genuinely non-vacuous** — unlike `ClayYangMillsTheorem` and `ClayYangMillsStrong` which use `sorry` in their hypotheses and are dischargeable by `False.elim`.

## Current Status: 3 Live Hypotheses

The formal deduction chain is **complete**. `ClayYangMillsPhysicalStrong` follows from exactly three remaining hypotheses:

| Hypothesis | Meaning | Est. progress |
|---|---|---|
| `FeynmanKacFormula` | Path-integral representation + distP ∈ ℕ | ~10% |
| `StateNormBound ψ_obs C_ψ` | Observation states are norm-bounded | ~40% |
| `HasSpectralGap T P₀ γ C` | Transfer matrix has spectral gap | ~25% |

**Eliminated in recent campaigns:**
- C103 (v1.19.0): `FeynmanKacToPhysicalStrong` — chains C102→C87-2, proves 4-hyp theorem
- C104 (v1.20.0): `DistPNonnegFromFormula` — derives `hdistP` from FK via `Nat.cast_nonneg`, reduces 4→3 hyps

**Overall genuine progress: ~22%**

## Repository Structure

```
YangMills/
  P8_PhysicalGap/           ← main campaign directory
    FeynmanKacBridge.lean    ← FeynmanKacFormula definition
    FeynmanKacToPhysicalStrong.lean  ← C103: 4-hyp chain
    DistPNonnegFromFormula.lean      ← C104: hdistP elimination
    OperatorNormBound.lean   ← C87: op-norm exp decay
    ...
  YangMills.lean             ← root imports
UNCONDITIONALITY_ROADMAP.md  ← full campaign log
STATE_OF_THE_PROJECT.md      ← current state
AI_ONBOARDING.md             ← for AI agents picking up the work
.claude/agents/librarian.md  ← doc-update agent spec
```

## Oracle Policy

Every theorem in P8_PhysicalGap must satisfy:

```
#print axioms <theorem> 
-- [propext, Classical.choice, Quot.sound]
```

Zero `sorry`. Zero new axioms. Non-negotiable.

## Campaign Loop

This project runs an **autonomous multi-agent loop**:

1. Strategist picks highest-value hypothesis to eliminate
2. Executor writes the Lean proof
3. Build + oracle check
4. Commit + tag + push
5. Librarian updates docs
6. GOTO 1

See `AI_ONBOARDING.md` for the full protocol.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build YangMills.P8_PhysicalGap.DistPNonnegFromFormula
```

## License

Apache 2.0
