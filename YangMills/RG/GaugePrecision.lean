/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AveragingAdjoint

/-!
# Gauge precision coercivity bookkeeping

This module records the source-independent Hilbert-space inequality behind the
P4 spectral/coercivity route.  If a block Poincare/Hodge estimate controls
`‖x‖²` by the sum of a positive background quadratic form and an adjoint
averaging mass `Q†Q`, then adding the mass with coefficient `a` gives a
coercive precision operator with constant `min 1 a / C_P`.

This is only the deterministic coercivity algebra.  It does not construct the
Yang--Mills gauge-fixed Hessian, prove a block Poincare theorem for gauge
fields, identify a physical propagator, prove covariance decay, or produce raw
polymer activities.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- Abstract adjoint-mass coercivity from a block Poincare/Hodge estimate.

The hypothesis

`‖x‖² ≤ C_P * (⟪x, K x⟫ + ‖Q x‖²)`

is the only analytic input.  The conclusion is pure Hilbert-space bookkeeping:
the precision `K + a Q†Q` dominates `(min 1 a / C_P) ‖x‖²`. -/
theorem coercive_add_adjointMass_of_blockPoincare
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K : E →L[ℝ] E) (Q : E →L[ℝ] F)
    {a CP : ℝ}
    (ha : 0 ≤ a) (hCP : 0 < CP)
    (hKnonneg : ∀ x : E, 0 ≤ inner ℝ x (K x))
    (hPoincare :
      ∀ x : E, ‖x‖ ^ 2 ≤ CP * (inner ℝ x (K x) + ‖Q x‖ ^ 2)) :
    ∀ x : E,
      (min 1 a / CP) * ‖x‖ ^ 2 ≤
        inner ℝ x ((K + a • (Q.adjoint.comp Q)) x) := by
  intro x
  let m : ℝ := min 1 a
  have hm0 : 0 ≤ m := by
    dsimp [m]
    exact le_min zero_le_one ha
  have hm_le_one : m ≤ 1 := by
    dsimp [m]
    exact min_le_left 1 a
  have hm_le_a : m ≤ a := by
    dsimp [m]
    exact min_le_right 1 a
  have hP' :
      ‖x‖ ^ 2 / CP ≤ inner ℝ x (K x) + ‖Q x‖ ^ 2 := by
    rw [div_le_iff₀ hCP]
    nlinarith [hPoincare x]
  have hscaled :
      m * (‖x‖ ^ 2 / CP) ≤
        m * (inner ℝ x (K x) + ‖Q x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hP' hm0
  have hleft :
      (m / CP) * ‖x‖ ^ 2 ≤
        m * (inner ℝ x (K x) + ‖Q x‖ ^ 2) := by
    calc
      (m / CP) * ‖x‖ ^ 2 = m * (‖x‖ ^ 2 / CP) := by ring
      _ ≤ m * (inner ℝ x (K x) + ‖Q x‖ ^ 2) := hscaled
  have hKpart :
      m * inner ℝ x (K x) ≤ inner ℝ x (K x) := by
    simpa using
      mul_le_mul_of_nonneg_right hm_le_one (hKnonneg x)
  have hQpart :
      m * ‖Q x‖ ^ 2 ≤ a * ‖Q x‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right hm_le_a (sq_nonneg ‖Q x‖)
  have hmass :
      inner ℝ x ((Q.adjoint.comp Q) x) = ‖Q x‖ ^ 2 := by
    dsimp
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have hprecision :
      inner ℝ x ((K + a • (Q.adjoint.comp Q)) x)
        = inner ℝ x (K x) + a * ‖Q x‖ ^ 2 := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_right, inner_smul_right, hmass]
  calc
    (min 1 a / CP) * ‖x‖ ^ 2
        = (m / CP) * ‖x‖ ^ 2 := by rfl
    _ ≤ m * (inner ℝ x (K x) + ‖Q x‖ ^ 2) := hleft
    _ ≤ inner ℝ x (K x) + a * ‖Q x‖ ^ 2 := by
        nlinarith [hKpart, hQpart]
    _ = inner ℝ x ((K + a • (Q.adjoint.comp Q)) x) := hprecision.symm

/-- The same coercivity inequality for the concrete scaled block average
`qMassCLM = Q†Q` already used by the finite RG averaging substrate. -/
theorem coercive_add_qMassCLM_of_blockPoincare
    {d L N' : ℕ} {V : Type*}
    [NeZero L] [NeZero N']
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype (ConcreteEdge d (L * N'))] [Fintype (ConcreteEdge d N')]
    (K : FineBondHilbert d L N' V →L[ℝ] FineBondHilbert d L N' V)
    (s : ℝ) {a CP : ℝ}
    (ha : 0 ≤ a) (hCP : 0 < CP)
    (hKnonneg :
      ∀ A : FineBondHilbert d L N' V, 0 ≤ inner ℝ A (K A))
    (hPoincare :
      ∀ A : FineBondHilbert d L N' V,
        ‖A‖ ^ 2 ≤
          CP * (inner ℝ A (K A) +
            ‖scaledLinAvgCLM (d := d) (V := V) s L N' A‖ ^ 2)) :
    ∀ A : FineBondHilbert d L N' V,
      (min 1 a / CP) * ‖A‖ ^ 2 ≤
        inner ℝ A ((K + a • qMassCLM (d := d) (V := V) s L N') A) := by
  simpa [qMassCLM] using
    coercive_add_adjointMass_of_blockPoincare
      (E := FineBondHilbert d L N' V)
      (F := CoarseBondHilbert d N' V)
      K (scaledLinAvgCLM (d := d) (V := V) s L N')
      ha hCP hKnonneg hPoincare

/-- Coercivity is stable under a quadratic-form perturbation whose negative
part is bounded by `δ ‖x‖²`.  This is the scalar perturbative closure that a
future gauge Hessian/background-field estimate can consume. -/
theorem coercive_add_perturbation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : E →L[ℝ] E) {c δ : ℝ}
    (hA : ∀ x : E, c * ‖x‖ ^ 2 ≤ inner ℝ x (A x))
    (hB : ∀ x : E, -δ * ‖x‖ ^ 2 ≤ inner ℝ x (B x)) :
    ∀ x : E,
      (c - δ) * ‖x‖ ^ 2 ≤ inner ℝ x ((A + B) x) := by
  intro x
  have hsum :
      c * ‖x‖ ^ 2 + (-δ * ‖x‖ ^ 2) ≤
        inner ℝ x (A x) + inner ℝ x (B x) :=
    add_le_add (hA x) (hB x)
  calc
    (c - δ) * ‖x‖ ^ 2
        = c * ‖x‖ ^ 2 + (-δ * ‖x‖ ^ 2) := by ring
    _ ≤ inner ℝ x (A x) + inner ℝ x (B x) := hsum
    _ = inner ℝ x ((A + B) x) := by
      rw [ContinuousLinearMap.add_apply, inner_add_right]

end YangMills.RG
