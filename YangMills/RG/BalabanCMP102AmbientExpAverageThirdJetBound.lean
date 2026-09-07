/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientExpAverageBudget
import YangMills.RG.BalabanCMP102AmbientLogAverageThirdJetBound
import YangMills.RG.ExpSecondDerivativeBound

/-!
# Third jet of the CMP98 exponential block average

This file propagates the source-generated jets of the normalized logarithmic
average through the literal noncommutative exponential.  The quantitative
Faà di Bruno bound uses only explicit Mercator, Wilson-line, and exponential
series budgets; no composite third-derivative estimate is supplied.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
  [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102AmbientExpAverageThirdJetMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

local instance cmp102AmbientExpAverageThirdJetCMLSeminormed (n : ℕ) :
    SeminormedAddCommGroup
      (PhysicalAmbientMatrixTangent d (M * N') Nc [×n]→L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousMultilinearMap.seminormedAddCommGroup

/-- A strictly enlarged logarithmic-average radius, suitable for both the
open-ball second-derivative theorem and the closed-ball third-derivative
theorem for the exponential series. -/
def cmp102SourceLogAverageNNRadius (q : NNReal) : NNReal :=
  ⟨cmp102SourceLogAverageRadius q + 1,
    add_nonneg (cmp102SourceLogAverageRadius_nonneg q.2) zero_le_one⟩

/-- One common budget for the value and first three jets of the outer
noncommutative exponential. -/
def cmp102SourceExpOrderThreeOuterBudget
    (q : NNReal) : ℝ :=
  let R := (cmp102SourceLogAverageNNRadius q : ℝ)
  max (cmp102SourceExpAverageValueBudget q)
    (max (expDerivativeBudget R)
      (max (expSecondDerivativeBudget R)
        (expThirdDerivativeBallBudget
          (A := Matrix (Fin Nc) (Fin Nc) ℂ)
          (cmp102SourceLogAverageNNRadius q))))

/-- The generated outer budget controls every exponential jet through
order three on the physical logarithmic-average ball. -/
theorem norm_iteratedFDeriv_exp_le_orderThreeOuterBudget
    (q : NNReal)
    {Y : Matrix (Fin Nc) (Fin Nc) ℂ}
    (hY : ‖Y‖ ≤ cmp102SourceLogAverageRadius q)
    (i : ℕ) (hi : i ≤ 3) :
    ‖iteratedFDeriv ℝ i
        (NormedSpace.exp :
          Matrix (Fin Nc) (Fin Nc) ℂ →
            Matrix (Fin Nc) (Fin Nc) ℂ) Y‖ ≤
      cmp102SourceExpOrderThreeOuterBudget (Nc := Nc) q := by
  have hR :
      cmp102SourceLogAverageRadius q <
        (cmp102SourceLogAverageNNRadius q : ℝ) := by
    simp [cmp102SourceLogAverageNNRadius]
  have hYlt :
      ‖Y‖ < (cmp102SourceLogAverageNNRadius q : ℝ) :=
    hY.trans_lt hR
  have hYwide :
      ‖Y‖ ≤ (cmp102SourceLogAverageNNRadius q : ℝ) :=
    hYlt.le
  interval_cases i
  · have hzero :
        ‖iteratedFDeriv ℝ 0
            (NormedSpace.exp :
              Matrix (Fin Nc) (Fin Nc) ℂ →
                Matrix (Fin Nc) (Fin Nc) ℂ) Y‖ =
          ‖NormedSpace.exp Y‖ :=
      norm_iteratedFDeriv_zero
    calc
      ‖iteratedFDeriv ℝ 0
          (NormedSpace.exp :
            Matrix (Fin Nc) (Fin Nc) ℂ →
              Matrix (Fin Nc) (Fin Nc) ℂ) Y‖ =
          ‖NormedSpace.exp Y‖ := hzero
      _ ≤ cmp102SourceExpAverageValueBudget q := by
        simpa [cmp102SourceExpAverageValueBudget] using
          norm_exp_le_derivativeBudgets
            (cmp102SourceLogAverageRadius_nonneg q.2) hY
      _ ≤ _ := le_max_left _ _
  · calc
      ‖iteratedFDeriv ℝ 1
          (NormedSpace.exp :
            Matrix (Fin Nc) (Fin Nc) ℂ →
              Matrix (Fin Nc) (Fin Nc) ℂ) Y‖ =
          ‖fderiv ℝ
            (NormedSpace.exp :
              Matrix (Fin Nc) (Fin Nc) ℂ →
                Matrix (Fin Nc) (Fin Nc) ℂ) Y‖ :=
        norm_iteratedFDeriv_one
          (𝕜 := ℝ) (x := Y)
          (NormedSpace.exp :
            Matrix (Fin Nc) (Fin Nc) ℂ →
              Matrix (Fin Nc) (Fin Nc) ℂ)
      _ ≤ expDerivativeBudget
          (cmp102SourceLogAverageNNRadius q) :=
        norm_fderiv_exp_le_derivativeBudget hYwide
      _ ≤ _ :=
        (le_max_left _ _).trans (le_max_right _ _)
  · exact
      (norm_iteratedFDeriv_two_exp_le_secondDerivativeBudget hYlt).trans
        ((le_max_left _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _)))
  · have hYnn : ‖Y‖₊ ≤ cmp102SourceLogAverageNNRadius q := by
      exact_mod_cast hYwide
    exact
      (norm_iteratedFDeriv_three_exp_le_ballBudget
        (cmp102SourceLogAverageNNRadius q) hYnn).trans
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _)))

/-- Inner radius used for the logarithmic-average jets in the outer
composition estimate. -/
def cmp102SourceLogAverageCompositionRadius
    (d M : ℕ) (r q : NNReal) : ℝ :=
  max 1
    (cmp102SourceLocalNearLogThirdJetBudget
      (Nc := Nc) d M r q)

/-- Fully generated third-jet budget for the literal CMP98 exponential
block average. -/
def cmp102SourceExpAverageThirdJetBudget
    (d M : ℕ) (r q : NNReal) : ℝ :=
  6 * cmp102SourceExpOrderThreeOuterBudget
        (Nc := Nc) q *
    cmp102SourceLogAverageCompositionRadius
        (Nc := Nc) d M r q ^ 3

set_option maxHeartbeats 1200000 in
/-- Every positive jet through order three of the literal exponential block
average is controlled by the same source-generated physical budget. -/
theorem norm_iteratedFDeriv_cmp98UbarExpAverage_le_sourceThirdJetBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r q : NNReal) (hZ : ‖Z‖ < r)
    (hq : (q : ℝ) < 1)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < q)
    (i : ℕ) (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    ‖iteratedFDeriv ℝ i (cmp98UbarExpAverage U b) Z‖ ≤
      cmp102SourceExpAverageThirdJetBudget
        (Nc := Nc) d M r q := by
  let inner := cmp98UbarLogAverage U b
  let outer :
      Matrix (Fin Nc) (Fin Nc) ℂ →
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    NormedSpace.exp
  let C := cmp102SourceExpOrderThreeOuterBudget
    (Nc := Nc) q
  let D := cmp102SourceLogAverageCompositionRadius
    (Nc := Nc) d M r q
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1 :=
    fun x hx => (hD x hx).trans hq
  have hinner : ContDiffAt ℝ i inner Z :=
    (analyticAt_cmp98UbarLogAverage_of_norm_lt_one U b Z hsmall
      ).contDiffAt.of_le le_top
  have houter : ContDiffAt ℝ i outer (inner Z) :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (inner Z)).contDiffAt.of_le le_top
  have hY :
      ‖inner Z‖ ≤ cmp102SourceLogAverageRadius q := by
    simpa [inner] using
      norm_cmp98UbarLogAverage_le_sourceBudget
        U b Z q.2 hq (fun x hx => (hD x hx).le)
  have hC : ∀ j, j ≤ i →
      ‖iteratedFDeriv ℝ j outer (inner Z)‖ ≤ C := by
    intro j hj
    exact norm_iteratedFDeriv_exp_le_orderThreeOuterBudget
      q hY j (hj.trans hi3)
  have hDone : 1 ≤ D := le_max_left _ _
  have hDjets : ∀ j, 1 ≤ j → j ≤ i →
      ‖iteratedFDeriv ℝ j inner Z‖ ≤ D ^ j := by
    intro j hj1 hji
    have hraw :
        ‖iteratedFDeriv ℝ j inner Z‖ ≤
          cmp102SourceLocalNearLogThirdJetBudget
            (Nc := Nc) d M r q := by
      exact
        norm_iteratedFDeriv_cmp98UbarLogAverage_le_sourceBudget
          U b Z r q hZ hq hD j hj1 (hji.trans hi3)
    calc
      ‖iteratedFDeriv ℝ j inner Z‖
          ≤ cmp102SourceLocalNearLogThirdJetBudget
              (Nc := Nc) d M r q := hraw
      _ ≤ D := le_max_right _ _
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ j := pow_le_pow_right₀ hDone hj1
  have hmain :=
    norm_iteratedFDeriv_comp_le_at_of_both_local
      houter hinner hC hDjets
  have hCnonneg : 0 ≤ C :=
    (norm_nonneg (iteratedFDeriv ℝ 0 outer (inner Z))).trans
      (hC 0 (Nat.zero_le i))
  have hDnonneg : 0 ≤ D := zero_le_one.trans hDone
  have hfac : (i.factorial : ℝ) ≤ 6 := by
    interval_cases i <;> norm_num
  have hpow : D ^ i ≤ D ^ 3 :=
    pow_le_pow_right₀ hDone hi3
  change
    ‖iteratedFDeriv ℝ i (outer ∘ inner) Z‖ ≤ _ at hmain
  change
    ‖iteratedFDeriv ℝ i (cmp98UbarExpAverage U b) Z‖ ≤ _
  calc
    ‖iteratedFDeriv ℝ i (cmp98UbarExpAverage U b) Z‖ =
        ‖iteratedFDeriv ℝ i (outer ∘ inner) Z‖ := rfl
    _ ≤ (i.factorial : ℝ) * C * D ^ i := hmain
    _ ≤ 6 * C * D ^ 3 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hfac hCnonneg) hpow
        (pow_nonneg hDnonneg i) (mul_nonneg (by norm_num) hCnonneg)
    _ = cmp102SourceExpAverageThirdJetBudget
        (Nc := Nc) d M r q := rfl

set_option maxHeartbeats 1200000 in
/-- The third derivative of the literal exponential block average is
controlled by source-generated physical budgets, uniformly in the ambient
periodic volume. -/
theorem norm_iteratedFDeriv_three_cmp98UbarExpAverage_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r q : NNReal) (hZ : ‖Z‖ < r)
    (hq : (q : ℝ) < 1)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < q) :
    ‖iteratedFDeriv ℝ 3 (cmp98UbarExpAverage U b) Z‖ ≤
      cmp102SourceExpAverageThirdJetBudget
        (Nc := Nc) d M r q :=
  norm_iteratedFDeriv_cmp98UbarExpAverage_le_sourceThirdJetBudget
    U b Z r q hZ hq hD 3 (by omega) (by omega)

end

end YangMills.RG
