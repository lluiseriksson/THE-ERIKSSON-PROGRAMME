# The Eriksson Programme: Machine-Verified Yang-Mills Mass Gap

**v1.21.0** | Lean 4.29.0-rc6 / Mathlib4 | Autonomous campaign loop active

## What This Is

A long-term Lean 4 formalization project targeting the **Yang-Mills existence and mass gap** problem (one of the Clay Millennium Problems). The goal is a fully machine-verified proof of `ClayYangMillsPhysicalStrong` with zero `sorry` and only standard axioms.

## The Non-Vacuous Target

```lean
theorem ClayYangMillsPhysicalStrong ... :
    ∃ C γ : ℝ, 0 < γ ∧ ∀ N p q,
      |wilsonConnectedCorr ... N p q| ≤ C * Real.exp (-γ * distP N p q)
```

This is **genuinely non-vacuous** — unlike `ClayYangMillsTheorem`/`ClayYangMillsStrong` (trivially true by `False.elim`).

## Current Status: 2 Live Hypotheses

The formal deduction chain is **complete**. `ClayYangMillsPhysicalStrong` follows from exactly two remaining hypotheses:

| Hypothesis | Meaning | Est. progress |
|---|---|---|
| `PhysicalFeynmanKacFormula` | FK + unit-norm obs states | ~10% |
| `HasSpectralGap T P₀ γ C` | Transfer matrix spectral gap | ~25% |

**Recently eliminated:**
- C103 (v1.19.0): `FeynmanKacToPhysicalStrong` — 4-hypothesis chain proven
- C104 (v1.20.0): `DistPNonnegFromFormula` — `hdistP` eliminated (FK ⇒ distP ∈ ℕ)
- C105 (v1.21.0): `UnitObsToPhysicalStrong` — `StateNormBound` absorbed (unit norm ⇒ C_ψ=1)

**Overall genuine progress: ~24%**

## Repository Structure

```
YangMills/
  P8_PhysicalGap/
    FeynmanKacBridge.lean           ← FeynmanKacFormula, StateNormBound defs
    FeynmanKacToPhysicalStrong.lean ← C103: 4-hyp chain
    DistPNonnegFromFormula.lean     ← C104: hdistP elimination
    UnitObsToPhysicalStrong.lean    ← C105: StateNormBound elimination
    OperatorNormBound.lean          ← C87: op-norm exp decay
    ...
  YangMills.lean                    ← root imports
UNCONDITIONALITY_ROADMAP.md
STATE_OF_THE_PROJECT.md
AI_ONBOARDING.md
.claude/agents/librarian.md
```

## Oracle Policy

Every P8_PhysicalGap theorem: `#print axioms` → `[propext, Classical.choice, Quot.sound]`. Zero `sorry`. Zero new axioms.

## Campaign Loop

1. Strategist picks target → 2. Executor writes Lean → 3. Build+oracle → 4. Commit+tag+push → 5. Docs → GOTO 1

See `AI_ONBOARDING.md` for full protocol.

## License

Apache 2.0
