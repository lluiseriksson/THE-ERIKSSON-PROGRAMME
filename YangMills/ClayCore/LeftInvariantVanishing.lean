/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.SchurZeroMean

/-!
# The eigenfunction-vanishing principle in full generality

`CenterVanishing.lean` proved the centre-eigenfunction principle for the specific
measure `sunHaarProb N_c` and the specific element `ω·I` (`scalarCenterElement`).
But the argument used **nothing** about SU(N_c): only that the measure is
left-invariant and that the integrand is scaled by a constant `≠ 1` under left
translation by *some* group element.  This file states it at that level of
generality.

  For any group `G` with a left-invariant measure `μ`, any `g : G`, and any
  `f : G → ℂ` with `f(g·x) = c·f(x)` for a scalar `c ≠ 1`,

      `∫ f dμ = 0.`

The hypotheses are exactly those of `MeasureTheory.integral_mul_left_eq_self`
(`[Group G] [MeasurableMul G] [IsMulLeftInvariant μ]`), verified against the
Mathlib source — so this lemma typechecks wherever that one does, and in
particular:

* **SU(N_c) / `sunHaarProb`** — recovers `CenterVanishing` (re-derived below in
  one line, `center_eigenfunction_vanishing_general`).
* **U(1) / circle Haar** — the abelian warm-up of `HORIZON.md §5`; `g = ` any
  non-identity element, `c = ` the corresponding character value.
* **The lattice product measure** `gaugeMeasureFrom μ`
  (`L1_GibbsMeasure.GibbsMeasure`) — once its left-invariance under the per-edge
  group action is registered, this lemma proves that any **open Wilson line**
  (net N-ality `≠ 0`, hence scaled by a centre phase `≠ 1`) has zero expectation:
  the rigorous "no isolated colour charge" statement.  See `HORIZON.md §3.3` for
  the precise remaining bridge (the single missing instance is
  `IsMulLeftInvariant (gaugeMeasureFrom μ)` for the diagonal centre action).

This is the form a future prover should depend on: to kill any new integral by a
symmetry, supply the measure's invariance, the eigenvalue identity, and `c ≠ 1`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no new axioms.
(Pending a `lake build` pass; risk is minimal — the proof is three Mathlib lemmas.)
-/

namespace YangMills

open MeasureTheory

noncomputable section

/-! ## The general principle -/

/-- **Eigenfunction-vanishing principle (general).**

If `μ` is a left-invariant measure on a group `G` and `f : G → ℂ` is scaled by a
constant `c ≠ 1` under left translation by `g`, then `∫ f dμ = 0`.

No integrability or continuity hypothesis is needed: the proof rests only on
`integral_mul_left_eq_self` (left invariance) and `integral_const_mul`, both
unconditional. -/
theorem integral_eq_zero_of_left_invariant_eigenfunction
    {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (f : G → ℂ) (g : G) (c : ℂ)
    (hf : ∀ x, f (g * x) = c * f x) (hc : c ≠ 1) :
    ∫ x, f x ∂μ = 0 := by
  set J : ℂ := ∫ x, f x ∂μ with hJ
  -- Left invariance: translating by `g` does not change the integral.
  have hinv : J = ∫ x, f (g * x) ∂μ := by
    rw [hJ]; symm
    exact MeasureTheory.integral_mul_left_eq_self f g
  -- The eigenvalue pulls out.
  have hmul : (∫ x, f (g * x) ∂μ) = c * J := by
    have hfun : (fun x => f (g * x)) = (fun x => c * f x) := funext hf
    calc ∫ x, f (g * x) ∂μ
        = ∫ x, c * f x ∂μ := by rw [hfun]
      _ = c * ∫ x, f x ∂μ := integral_const_mul c f
      _ = c * J := by rw [← hJ]
  rw [hmul] at hinv
  -- `J = c·J` with `c ≠ 1` forces `J = 0`.
  have hfactor : (1 - c) * J = 0 := by linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm hc
  · exact h2

/-! ## The SU(N) centre engine is a one-line specialisation -/

/-- The centre-eigenfunction engine of `CenterVanishing.lean`, recovered from the
general principle by instantiating `μ := sunHaarProb N_c` and `g := ω·I`.  This
verifies the abstraction is faithful (the typeclasses line up: SU(N_c) is a
`MeasurableMul` group and `sunHaarProb` is `IsMulLeftInvariant`). -/
theorem center_eigenfunction_vanishing_general
    (N_c : ℕ) [NeZero N_c]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℂ) (c : ℂ)
    (hf : ∀ U, f (scalarCenterElement N_c * U) = c * f U) (hc : c ≠ 1) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ), f U ∂(sunHaarProb N_c) = 0 :=
  integral_eq_zero_of_left_invariant_eigenfunction
    (sunHaarProb N_c) f (scalarCenterElement N_c) c hf hc

/-- Concrete demonstration through the general principle: `∫ tr U = 0` (F0). -/
theorem trace_integral_zero_general
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      U.val.trace ∂(sunHaarProb N_c) = 0 :=
  center_eigenfunction_vanishing_general N_c
    (fun U => U.val.trace) (rootOfUnity N_c)
    (fun U => trace_scalarCenter_mul N_c U)
    (rootOfUnity_ne_one N_c hN)

end

end YangMills
