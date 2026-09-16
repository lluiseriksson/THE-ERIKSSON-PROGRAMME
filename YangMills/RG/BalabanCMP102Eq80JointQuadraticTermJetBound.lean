/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80JointTransportTermJetBound

/-!
# Quantitative joint-jet bound for the equation-(80) quadratic term

The third literal term in CMP102 equation (80) is

`(1 / 2) ⟪H (D A'), Δπ (H (D A'))⟫`.

We first package the explicit binomial bound for the joint evaluation
`(H,A') ↦ H (D A')`.  The quadratic term is then controlled by a second
bilinear Leibniz sum, with the literal factor `1 / 2` and the exact operator
norm `‖Δπ‖`.  The package contains only derivatives of `H`, `D`, and the
coordinate projections; it is not a bound for the full equation-(80)
potential.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev JointSpace := (F →L[ℝ] E) × E

/-- Explicit binomial majorant for the joint evaluation
`(H,A') ↦ H (D A')`. -/
noncomputable def cmp102Eq80JointEvaluationJetMajorant
    (D : E → F) (n : ℕ)
    (p : JointSpace (E := E) (F := F)) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i
        (fun q : JointSpace (E := E) (F := F) => q.1) p‖ *
      ‖iteratedFDeriv ℝ (n - i)
        (fun q : JointSpace (E := E) (F := F) => D q.2) p‖

/-- The explicit joint-evaluation majorant is nonnegative. -/
theorem cmp102Eq80JointEvaluationJetMajorant_nonneg
    (D : E → F) (n : ℕ)
    (p : JointSpace (E := E) (F := F)) :
    0 ≤ cmp102Eq80JointEvaluationJetMajorant D n p := by
  unfold cmp102Eq80JointEvaluationJetMajorant
  refine Finset.sum_nonneg fun i hi => ?_
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (norm_nonneg
        (iteratedFDeriv ℝ i
          (fun q : JointSpace (E := E) (F := F) => q.1) p)))
    (norm_nonneg
      (iteratedFDeriv ℝ (n - i)
        (fun q : JointSpace (E := E) (F := F) => D q.2) p))

/-- The joint evaluation is bounded directly by its explicit binomial
majorant. -/
theorem norm_iteratedFDeriv_cmp102Eq80JointEvaluation_le
    (D : E → F) (hD : ContDiff ℝ ⊤ D)
    (n : ℕ) (p : JointSpace (E := E) (F := F)) :
    ‖iteratedFDeriv ℝ n
        (fun q : JointSpace (E := E) (F := F) => q.1 (D q.2)) p‖ ≤
      cmp102Eq80JointEvaluationJetMajorant D n p := by
  unfold cmp102Eq80JointEvaluationJetMajorant
  simpa using
    (norm_iteratedFDeriv_clm_apply
      (contDiff_fst :
        ContDiff ℝ ⊤
          (fun q : JointSpace (E := E) (F := F) => q.1))
      (hD.comp contDiff_snd) p le_top)

/-- The literal quadratic jet is controlled by the convolution of two
source-generated joint-evaluation majorants. -/
theorem norm_iteratedFDeriv_cmp102Eq80JointQuadraticTerm_le
    (D : E → F) (Δπ : E →L[ℝ] E) (hD : ContDiff ℝ ⊤ D)
    (n : ℕ) (p : JointSpace (E := E) (F := F)) :
    ‖iteratedFDeriv ℝ n (cmp102Eq80JointQuadraticTerm D Δπ) p‖ ≤
      (1 / 2 : ℝ) *
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) *
            cmp102Eq80JointEvaluationJetMajorant D i p *
            (‖Δπ‖ *
              cmp102Eq80JointEvaluationJetMajorant D (n - i) p) := by
  let HD : JointSpace (E := E) (F := F) → E :=
    fun q => q.1 (D q.2)
  have hHD : ContDiff ℝ ⊤ HD :=
    contDiff_fst.clm_apply (hD.comp contDiff_snd)
  let pairing : JointSpace (E := E) (F := F) → ℝ :=
    fun q => (innerSL ℝ) (HD q) (Δπ (HD q))
  have hpairing : ContDiff ℝ ⊤ pairing :=
    hHD.inner ℝ (Δπ.contDiff.comp hHD)
  let half : ℝ →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hhalf : ‖half‖ = (1 / 2 : ℝ) := by
    rw [show half =
      (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ by rfl,
      norm_smul, ContinuousLinearMap.norm_id]
    norm_num
  have hquadratic :
      cmp102Eq80JointQuadraticTerm D Δπ =
        half ∘ pairing := by
    funext q
    simp [half, pairing, HD, cmp102Eq80JointQuadraticTerm]
  rw [hquadratic]
  apply
    (half.norm_iteratedFDeriv_comp_left
      hpairing.contDiffAt le_top).trans
  rw [hhalf]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change
    ‖iteratedFDeriv ℝ n
        (fun q => (innerSL ℝ) (HD q) (Δπ (HD q))) p‖ ≤ _
  apply
    ((innerSL ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
      hHD (Δπ.contDiff.comp hHD) p le_top
        (norm_innerSL_le ℝ (E := E))).trans
  refine Finset.sum_le_sum fun i hi => ?_
  have hleft :
      ‖iteratedFDeriv ℝ i HD p‖ ≤
        cmp102Eq80JointEvaluationJetMajorant D i p :=
    norm_iteratedFDeriv_cmp102Eq80JointEvaluation_le
      D hD i p
  have hcomp :
      ‖iteratedFDeriv ℝ (n - i) (fun q => Δπ (HD q)) p‖ ≤
        ‖Δπ‖ * ‖iteratedFDeriv ℝ (n - i) HD p‖ :=
    Δπ.norm_iteratedFDeriv_comp_left hHD.contDiffAt le_top
  have hright :
      ‖iteratedFDeriv ℝ (n - i) (fun q => Δπ (HD q)) p‖ ≤
        ‖Δπ‖ *
          cmp102Eq80JointEvaluationJetMajorant D (n - i) p :=
    hcomp.trans <|
      mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_cmp102Eq80JointEvaluation_le
          D hD (n - i) p)
        (norm_nonneg Δπ)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hleft (by positivity)
  · exact hright
  · positivity
  · exact mul_nonneg (by positivity)
      (cmp102Eq80JointEvaluationJetMajorant_nonneg D i p)

end

end YangMills.RG
