/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.AbelianU1Unconditional
import YangMills.L6_FeynmanKac.FeynmanKac

/-!
# SU(1) discharge of `FeynmanKacWilsonBridge`

This module provides unconditional inhabitants for the predicates
defined in `L6_FeynmanKac/FeynmanKac.lean`:

* `FeynmanKacWilsonBridge` — fixed-volume bridge from spectral gap to
  Wilson decay.
* `FeynmanKacWilsonBridgeUniform` — uniform-in-N version.

Both predicates assert: given any spectral gap `(γ, C)` of an abstract
transfer operator `T` (with `0 < γ`, `0 < C`), the connected Wilson
correlator decays exponentially. For SU(1) this is **vacuously true**
because the connected Wilson correlator is identically zero
(Phase 49 mechanism via `wilsonConnectedCorr_su1_eq_zero`), so the
LHS of the inequality is `|0| = 0` and the RHS `C · exp(...) ≥ 0`.

## Caveat

Same trivial-group physics-degeneracy of Findings 003 + 011 + 012
applies. For `N_c ≥ 2`, the Feynman-Kac bridge encodes the actual
Branch III content: spectral-gap-of-transfer-operator implies
exponential Wilson decay. That requires the full Glimm-Jaffe / OS
construction.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills

open MeasureTheory Real

/-! ## §1. `FeynmanKacWilsonBridge` for SU(1) — unconditional -/

/-- **`FeynmanKacWilsonBridge` discharged unconditionally for SU(1)**,
    with arbitrary observable `F`, arbitrary distance, arbitrary
    Hilbert space, and arbitrary transfer / projector operators
    `T, P₀`. The Wilson connected correlator on SU(1) vanishes
    identically, so any exponential bound holds. -/
theorem feynmanKacWilsonBridge_su1
    {d N : ℕ} [NeZero d] [NeZero N]
    (β : ℝ) (F : ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (distP : ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T P₀ : H →L[ℝ] H) :
    FeynmanKacWilsonBridge
      (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β F distP T P₀ := by
  intro γ C hgap p q
  -- Wilson connected correlator vanishes for SU(1)
  rw [wilsonConnectedCorr_su1_eq_zero]
  rw [abs_zero]
  -- Goal: 0 ≤ C * exp(-γ * distP p q)
  exact mul_nonneg hgap.2.1.le (Real.exp_nonneg _)

#print axioms feynmanKacWilsonBridge_su1

/-! ## §2. `FeynmanKacWilsonBridgeUniform` for SU(1) — unconditional -/

/-- **`FeynmanKacWilsonBridgeUniform` discharged unconditionally for SU(1)**,
    the uniform-in-N version. Same vanishing argument as Phase 57 §1,
    universally quantified over lattice volume `N`. -/
theorem feynmanKacWilsonBridgeUniform_su1
    {d : ℕ} [NeZero d]
    (β : ℝ) (F : ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (distP : ∀ N : ℕ, ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T P₀ : H →L[ℝ] H) :
    FeynmanKacWilsonBridgeUniform
      (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β F distP T P₀ := by
  intro γ C hgap N _instN p q
  -- For each N, Wilson connected correlator on SU(1) vanishes
  rw [wilsonConnectedCorr_su1_eq_zero]
  rw [abs_zero]
  exact mul_nonneg hgap.2.1.le (Real.exp_nonneg _)

#print axioms feynmanKacWilsonBridgeUniform_su1

/-! ## §3. Coordination note -/

/-
After Phase 57, the SU(1) **structural-completeness frontier**
includes the L6_FeynmanKac layer:

```
Predicate                        SU(1)?  Phase
─────────────────────────────────────────────────
FeynmanKacWilsonBridge           ✓       57  -- NEW
FeynmanKacWilsonBridgeUniform    ✓       57  -- NEW
```

Combined SU(1) inhabited-predicate total after Phase 57: **22**.

The trivial-group physics-degeneracy carries forward (Finding 003).
For `N_c ≥ 2`, both predicates encode the substantive Branch III
spectral-gap → Wilson-decay implication, which requires the full
Glimm-Jaffe / Osterwalder-Seiler / Bałaban-RG infrastructure.

Cross-references:
- `FeynmanKac.lean` — predicate definitions.
- `AbelianU1Unconditional.lean` — `wilsonConnectedCorr_su1_eq_zero`.
- `COWORK_FINDINGS.md` Findings 003 + 011 + 012 — caveats.
-/

end YangMills
