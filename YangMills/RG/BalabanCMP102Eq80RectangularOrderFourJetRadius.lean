/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80CorrectedRectangularSourceJetBound

/-!
# Source-generated order-four radius for the equation-(80) inner map

The third physical field derivative of a reconstructed domain coefficient
uses the order-four joint jet of the global equation-(80) potential.  Its
Faà di Bruno remainder theorem previously received a power radius `Rjet`
for the complete inner map.

This module derives that radius from the literal value and first four jets
of the correction map `D`, together with the norm of the rectangular
operator `H`.  No bound for the complete potential, a completed activity, or
a domain-dependent source map is assumed.
-/

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev JointSpace := (F →L[ℝ] E) × E

/-- A single radius containing the four positive inner-map jet orders. -/
def cmp102Eq80RectangularOrderFourJetRadius
    (Hnorm B₀ B₁ B₂ B₃ B₄ : ℝ) : ℝ :=
  1 + B₀ + 2 * B₁ + 3 * B₂ + 4 * B₃ + B₄ +
    Hnorm * (B₁ + B₂ + B₃ + B₄)

/-- Literal correction jets through order four generate the power radius
used by the order-four equation-(80) source majorant. -/
theorem cmp102Eq80JointRemainderRadius_orderFour_of_correctionJets
    (D : E → F) (hD : ContDiff ℝ ⊤ D)
    (H : F →L[ℝ] E) (A : E)
    (B₀ B₁ B₂ B₃ B₄ : ℝ)
    (h₀ : ‖D A‖ ≤ B₀)
    (h₁ : ‖iteratedFDeriv ℝ 1 D A‖ ≤ B₁)
    (h₂ : ‖iteratedFDeriv ℝ 2 D A‖ ≤ B₂)
    (h₃ : ‖iteratedFDeriv ℝ 3 D A‖ ≤ B₃)
    (h₄ : ‖iteratedFDeriv ℝ 4 D A‖ ≤ B₄)
    (i : ℕ) (hi₁ : 1 ≤ i) (hi₄ : i ≤ 4) :
    ‖iteratedFDeriv ℝ i
        (fun q : JointSpace (E := E) (F := F) => q.2) (H, A)‖ +
        cmp102Eq80JointEvaluationJetMajorant D i (H, A) ≤
      cmp102Eq80RectangularOrderFourJetRadius
        ‖H‖ B₀ B₁ B₂ B₃ B₄ ^ i := by
  have hB₀ : 0 ≤ B₀ := (norm_nonneg (D A)).trans h₀
  have hB₁ : 0 ≤ B₁ :=
    (norm_nonneg (iteratedFDeriv ℝ 1 D A)).trans h₁
  have hB₂ : 0 ≤ B₂ :=
    (norm_nonneg (iteratedFDeriv ℝ 2 D A)).trans h₂
  have hB₃ : 0 ≤ B₃ :=
    (norm_nonneg (iteratedFDeriv ℝ 3 D A)).trans h₃
  have hB₄ : 0 ≤ B₄ :=
    (norm_nonneg (iteratedFDeriv ℝ 4 D A)).trans h₄
  have h₁' : ‖fderiv ℝ D A‖ ≤ B₁ := by
    simpa only [norm_iteratedFDeriv_one] using h₁
  let R :=
    cmp102Eq80RectangularOrderFourJetRadius
      ‖H‖ B₀ B₁ B₂ B₃ B₄
  have hRone : 1 ≤ R := by
    dsimp [R, cmp102Eq80RectangularOrderFourJetRadius]
    nlinarith [mul_nonneg (norm_nonneg H)
      (add_nonneg (add_nonneg (add_nonneg hB₁ hB₂) hB₃) hB₄)]
  have hlinear :
      cmp102Eq80JointFieldProjectionJetMajorant i +
          cmp102Eq80JointEvaluationSourceJetMajorant D i (H, A) ≤ R := by
    interval_cases i
    · have heval :
          cmp102Eq80JointEvaluationSourceJetMajorant D 1 (H, A) =
            ‖H‖ * ‖iteratedFDeriv ℝ 1 D A‖ + ‖D A‖ := by
        simp [cmp102Eq80JointEvaluationSourceJetMajorant,
          cmp102Eq80JointOperatorProjectionJetMajorant,
          Finset.sum_range_succ, norm_iteratedFDeriv_zero]
      rw [heval]
      simp [cmp102Eq80JointFieldProjectionJetMajorant]
      have hH :
          ‖H‖ * ‖fderiv ℝ D A‖ ≤ ‖H‖ * B₁ :=
        mul_le_mul_of_nonneg_left h₁' (norm_nonneg H)
      dsimp [R, cmp102Eq80RectangularOrderFourJetRadius]
      nlinarith [hH, h₀,
        mul_nonneg (norm_nonneg H)
          (add_nonneg (add_nonneg hB₂ hB₃) hB₄)]
    · have heval :
          cmp102Eq80JointEvaluationSourceJetMajorant D 2 (H, A) =
            ‖H‖ * ‖iteratedFDeriv ℝ 2 D A‖ +
              2 * ‖iteratedFDeriv ℝ 1 D A‖ := by
        simp [cmp102Eq80JointEvaluationSourceJetMajorant,
          cmp102Eq80JointOperatorProjectionJetMajorant,
          Finset.sum_range_succ]
      rw [heval]
      simp [cmp102Eq80JointFieldProjectionJetMajorant]
      have hH :
          ‖H‖ * ‖iteratedFDeriv ℝ 2 D A‖ ≤ ‖H‖ * B₂ :=
        mul_le_mul_of_nonneg_left h₂ (norm_nonneg H)
      dsimp [R, cmp102Eq80RectangularOrderFourJetRadius]
      nlinarith [hH, h₁',
        mul_nonneg (norm_nonneg H)
          (add_nonneg (add_nonneg hB₁ hB₃) hB₄)]
    · have heval :
          cmp102Eq80JointEvaluationSourceJetMajorant D 3 (H, A) =
            ‖H‖ * ‖iteratedFDeriv ℝ 3 D A‖ +
              3 * ‖iteratedFDeriv ℝ 2 D A‖ := by
        simp [cmp102Eq80JointEvaluationSourceJetMajorant,
          cmp102Eq80JointOperatorProjectionJetMajorant,
          Finset.sum_range_succ]
      rw [heval]
      simp [cmp102Eq80JointFieldProjectionJetMajorant]
      have hH :
          ‖H‖ * ‖iteratedFDeriv ℝ 3 D A‖ ≤ ‖H‖ * B₃ :=
        mul_le_mul_of_nonneg_left h₃ (norm_nonneg H)
      dsimp [R, cmp102Eq80RectangularOrderFourJetRadius]
      nlinarith [hH, h₂,
        mul_nonneg (norm_nonneg H)
          (add_nonneg (add_nonneg hB₁ hB₂) hB₄)]
    · have heval :
          cmp102Eq80JointEvaluationSourceJetMajorant D 4 (H, A) =
            ‖H‖ * ‖iteratedFDeriv ℝ 4 D A‖ +
              4 * ‖iteratedFDeriv ℝ 3 D A‖ := by
        simp [cmp102Eq80JointEvaluationSourceJetMajorant,
          cmp102Eq80JointOperatorProjectionJetMajorant,
          Finset.sum_range_succ]
      rw [heval]
      simp [cmp102Eq80JointFieldProjectionJetMajorant]
      have hH :
          ‖H‖ * ‖iteratedFDeriv ℝ 4 D A‖ ≤ ‖H‖ * B₄ :=
        mul_le_mul_of_nonneg_left h₄ (norm_nonneg H)
      dsimp [R, cmp102Eq80RectangularOrderFourJetRadius]
      nlinarith [hH, h₃,
        mul_nonneg (norm_nonneg H)
          (add_nonneg (add_nonneg hB₁ hB₂) hB₃)]
  calc
    ‖iteratedFDeriv ℝ i
          (fun q : JointSpace (E := E) (F := F) => q.2) (H, A)‖ +
        cmp102Eq80JointEvaluationJetMajorant D i (H, A) ≤
      cmp102Eq80JointFieldProjectionJetMajorant i +
        cmp102Eq80JointEvaluationSourceJetMajorant D i (H, A) :=
      add_le_add
        (norm_iteratedFDeriv_jointFieldProjection_le i hi₁ (H, A))
        (cmp102Eq80JointEvaluationJetMajorant_le_sourceJetMajorant
          D hD i (H, A))
    _ ≤ R := hlinear
    _ = R ^ 1 := by simp
    _ ≤ R ^ i := pow_le_pow_right₀ hRone hi₁
    _ = _ := by rfl

end

end YangMills.RG
