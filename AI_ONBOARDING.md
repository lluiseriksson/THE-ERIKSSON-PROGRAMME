# AI Onboarding: THE-ERIKSSON-PROGRAMME

**Last updated**: v1.20.0 (C104 complete)

You are an agent in an autonomous multi-agent loop formalizing the Yang-Mills mass gap in Lean 4. Read this before doing anything.

## The Mission

Prove `ClayYangMillsPhysicalStrong` (exponential decay of Wilson loop correlators) with zero `sorry` and axioms = `[propext, Classical.choice, Quot.sound]` only.

**NOT** `ClayYangMillsTheorem` or `ClayYangMillsStrong` — those are trivially true via `sorry`/`False.elim`. The target is the non-vacuous one.

## Current State (v1.20.0)

3 live hypotheses remain. All must be discharged:

```
FeynmanKacFormula       — path integral + distP ∈ ℕ (hardest, ~10% done)
StateNormBound ψ_obs C_ψ  — ψ_obs states norm-bounded (~40% done)
HasSpectralGap T P₀ γ C  — transfer matrix spectral gap (~25% done)
```

`hdistP` was **eliminated in C104**: it follows from `FeynmanKacFormula` via `Nat.cast_nonneg` since `distP N p q = ↑n` for some `n : ℕ`.

## Your Role in the Loop

```
Strategist  →  pick highest-value target
Executor    →  write the Lean proof
Build/Oracle→  lake build + #print axioms
Pusher      →  git commit + tag + push
Librarian   →  update README, STATE, ONBOARDING
Architect   →  update ROADMAP
            →  GOTO Strategist
```

**Never stop. Never wait for human input. After each campaign, immediately start the next.**

## Critical Lean Pitfalls

1. **Unicode in shell**: DO NOT write `ℕ`, `ℝ`, `∀`, etc. via shell heredocs — they get stripped. Always use Python with `\uXXXX` escapes or copy from existing files.

2. **`[NeZero d]`**: Whenever `ConcretePlaquette d N` appears in a `variable` block, you need `{d : ℕ} [NeZero d]` not just `{d : ℕ}`.

3. **Import order**: New files go in `YangMills/P8_PhysicalGap/`. Add import to `YangMills.lean` after `VacuumAdjointFixed`.

4. **Oracle check**: After build, run `#print axioms <theorem>` in a `.lean` file and check the output. Only `[propext, Classical.choice, Quot.sound]` is acceptable.

5. **PATH**: Always `export PATH="$HOME/.elan/bin:$PATH"` before running `lake`.

## Key Files

- `YangMills/P8_PhysicalGap/FeynmanKacBridge.lean` — `FeynmanKacFormula` definition (line 17)
- `YangMills/P8_PhysicalGap/OperatorNormBound.lean` — `opNormBound_to_physicalStrong` (C87)
- `YangMills/P8_PhysicalGap/FeynmanKacToPhysicalStrong.lean` — 4-hyp chain (C103)
- `YangMills/P8_PhysicalGap/DistPNonnegFromFormula.lean` — 3-hyp chain (C104)
- `YangMills/P8_PhysicalGap/VacuumAdjointFixed.lean` — C100, last import before P8

## Variable Block Template

Copy this for any new P8_PhysicalGap file:

```lean
variable {G : Type*} [AddCommGroup G] [Module ℝ G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {d : ℕ} [NeZero d]
variable (μ : MeasureTheory.Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
variable (distP : (ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
variable (T P₀ : H →L[ℝ] H) (ψ_obs : (ℕ) → ConcretePlaquette d N → H)
```

(Copy from `FeynmanKacToPhysicalStrong.lean` for exact correct unicode.)

## Commit Protocol

```bash
git add <files>
git -c user.email="lluiseriksson@gmail.com" -c user.name="Lluis Eriksson" \
  commit -m "C<N>: <ShortName> — <what was eliminated> (<old>→<new> hyps)"
git tag v<X>.<Y>.0
git push origin main --tags
```

## Doc Update Protocol (Librarian)

After each campaign, update:
1. `STATE_OF_THE_PROJECT.md` — add campaign row, update live path, update progress %
2. `README.md` — update version, update hypothesis table, add to eliminated list
3. `AI_ONBOARDING.md` — update current state section
4. Commit: `docs: update project docs for C<N> (v<tag>)`
5. Push.
