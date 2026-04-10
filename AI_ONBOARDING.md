# AI_ONBOARDING

Mandatory entry point for any AI session on this repository.

## 1. What This Project Is

Lean 4 formalization targeting `ClayYangMillsPhysicalStrong` (exponential decay of Wilson connected correlators). Reducing it to minimal named hypotheses.

**Current tag**: v1.18.0 (C102 complete, C103 in progress)

## 2. The Non-Vacuous Target

`ClayYangMillsTheorem` and `ClayYangMillsStrong` are **vacuous** (provable by trivial witnesses).
The genuine goal:

```lean
ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP
-- ∀ N p q, |W_cc(N,p,q)| ≤ C · exp(−γ · distP N p q)
```

## 3. Live Hypotheses (4 as of v1.18.0)

1. `FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs`
2. `StateNormBound ψ_obs C_ψ`
3. `HasSpectralGap T P₀ γ C_gap`
4. `hdistP : ∀ N [ΞNeZero NΟ] p q, 0 ≤ distP N p q`

## 4. Campaign Loop

1. Identify weakest live hypothesis
2. Write `.lean` in `YangMills/P8_PhysicalGap/` deriving it from weaker assumptions
3. Patch `YangMills.lean` imports
4. Update `UNCONDITIONALITY_ROADMAP.md`
5. Run `lake build <target>` + oracle check
6. Commit + tag + push
7. **Librarian updates docs** (README, STATE_OF_THE_PROJECT, AI_ONBOARDING)

## 5. Multi-Agent Roles

| Role | Responsibility |
|------|---------------|
| strategist | Decides which hypothesis to eliminate next |
| executor | Writes Lean file + deploy script |
| librarian | Updates all doc files (see `.claude/agents/librarian.md`) |
| architect | Checks structural consistency |

## 6. Key Files

```
YangMills.lean                              # root import (patch each campaign)
UNCONDITIONALITY_ROADMAP.md                 # full campaign log
STATE_OF_THE_PROJECT.md                     # current state snapshot
YangMills/P8_PhysicalGap/
  OperatorNormBound.lean                    # C87: core decay theorem
  FeynmanKacOpNormFromFormula.lean          # C102: Cauchy-Schwarz bridge
  FeynmanKacToPhysicalStrong.lean           # C103: in progress
```

## 7. Common Lean Pitfalls

- Always add `[NeZero d]` when using `ConcretePlaquette d N`
- `opNormBound_to_physicalStrong` is in `OperatorNormBound.lean`, section `BanachSpace`
- `feynmanKacOpNormBound_of_formula_stateNorm` is in `FeynmanKacOpNormFromFormula.lean`
- FK witness order: `⟨n, hn_dist, hn_eq⟩`

## 8. Oracle Policy

```
#print axioms YangMills.<theorem>
-- Required: [propext, Classical.choice, Quot.sound]
-- Forbidden: sorry, any new axiom
```
