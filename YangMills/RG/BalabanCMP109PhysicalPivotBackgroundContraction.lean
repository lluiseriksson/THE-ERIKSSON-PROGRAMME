/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalBackgroundBaseBudget
import YangMills.RG.BalabanCMP102PhysicalRightVariationBackgroundLipschitz
import YangMills.RG.BalabanCMP109PhysicalPivotFlat

/-!
# Small-background contraction of the physical CMP109 pivot defect

This module compares the literal CMP109 pivot response with its exactly
calibrated flat-background value.  The comparison is rowwise because the
physical contour geometry has already removed all off-diagonal pivot
responses.  Each surviving row is then the difference of the actual CMP98
right variations constructed from the represented nonlinear block.

The parameter `epsilon0` below is the formal positive-link small-background radius
used to instantiate the CMP109 regular-background regime (compare the source
condition near printed pages 249--251).  The exact source-to-Lean dictionary
from CMP109's `ε₀` to `PhysicalWilsonSmallBackground U epsilon0` remains
visible; this theorem does not silently identify the two.  In particular,
`epsilon0` is not the
CMP116 small-field cutoff radius `epsilon1 / gk`.  The inserted coarse tangent
remains arbitrary; no cutoff bound on that tangent is used.

The only final smallness condition is the explicit scalar inequality
`cmp109PhysicalPivotBackgroundBudget d L Nc epsilon0 < 1`.  Thus the Neumann
contraction is derived from the physical background comparison rather than
supplied as an operator hypothesis.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

local instance cmp109PhysicalPivotCoordCLMNorm :
    Norm (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp109PhysicalPivotCoordCLMSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp109PhysicalPivotCoordCLMNormedSpace :
    NormedSpace ℝ
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 2000000

/-- The literal linear constraint is the physical CMP98 right variation,
transported back to canonical Lie coordinates. -/
theorem cmp109PhysicalLinearConstraint_eq_retractedRightVariation
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc)
    (b : PhysicalBond d N')
    (hbase : ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp109PhysicalLinearConstraint U A b =
      cmp98AmbientToLieCoordCLM Nc
        (cmp98Eq119NonlinearRightVariation U A b) := by
  rw [cmp109PhysicalLinearConstraint_apply,
    cmp102PhysicalCochainToAmbientCLM_apply]
  rw [← cmp98Eq119NonlinearBlockInverseAtZero_twoField_eq U A 0 b]
  exact congrArg (cmp98AmbientToLieCoordCLM Nc)
    (cmp98Eq119NonlinearRightVariation_eq_ambientFDeriv
      U A b hbase).symm

/-- The source sup norm of a one-bond probe is exactly the norm of its
inserted Lie coordinate. -/
@[simp] theorem cmp98SourceFieldSupNorm_singlePhysicalBondCochain
    {d M N' Nc : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (p : PhysicalBond d (M * N')) (v : SUNLieCoord Nc) :
    cmp98SourceFieldSupNorm
        (singlePhysicalBondCochain
          (d := d) (N := M * N') (Nc := Nc) p v) =
      ‖v‖ := by
  apply le_antisymm
  · unfold cmp98SourceFieldSupNorm
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, _hq, rfl⟩
    by_cases hqp : q = p
    · subst q
      simp
    · rw [singlePhysicalBondCochain_of_ne v hqp, norm_zero]
      exact norm_nonneg v
  · have h := norm_apply_le_cmp98SourceFieldSupNorm
      (singlePhysicalBondCochain
        (d := d) (N := M * N') (Nc := Nc) p v) p
    simpa only [singlePhysicalBondCochain_self] using h

/-- Explicit volume-independent coefficient controlling the CMP109 pivot
defect at background radius `epsilon0`.  The fixed chart radius is the source value
`1/3`; the factor `L^(d-1)` is the literal sparse-pivot normalization. -/
def cmp109PhysicalPivotBackgroundBudget
    (d L Nc : ℕ) [NeZero Nc] (epsilon0 : ℝ) : ℝ :=
  ‖cmp98AmbientToLieCoordCLM Nc‖ *
    cmp102PhysicalRightVariationBackgroundBudget d L (1 / 3) epsilon0 *
    (L : ℝ) ^ (d - 1)

theorem cmp109PhysicalPivotBackgroundBudget_nonneg
    {d L Nc : ℕ} [NeZero Nc] {epsilon0 : ℝ}
    (hepsilon0 : 0 ≤ epsilon0) :
    0 ≤ cmp109PhysicalPivotBackgroundBudget d L Nc epsilon0 := by
  unfold cmp109PhysicalPivotBackgroundBudget
  exact mul_nonneg
    (mul_nonneg (norm_nonneg _)
      (cmp102PhysicalRightVariationBackgroundBudget_nonneg
        (by norm_num) hepsilon0))
    (by positivity)

/-- Pointwise physical pivot-defect bound.  No ambient-volume factor appears:
after exact no-mixing, row `b` depends only on the matching sparse probe. -/
theorem norm_cmp109PhysicalPivotDefectCLM_apply_le_backgroundBudget
    (hd : 2 ≤ d) (hL : 2 ≤ L) (hN' : 2 ≤ N')
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (epsilon0 : ℝ) (hepsilon0 : 0 ≤ epsilon0)
    (hsmall : PhysicalWilsonSmallBackground U epsilon0)
    (hradius : cmp99SourceUbarFineDeviationRadius d L epsilon0 ≤ 1 / 3)
    (D : CoarsePhysicalOneCochain d N' Nc)
    (b : PhysicalBond d N') :
    ‖cmp109PhysicalPivotDefectCLM U D b‖ ≤
      cmp109PhysicalPivotBackgroundBudget d L Nc epsilon0 * ‖D b‖ := by
  let U0 := trivialPhysicalGaugeBackground d (L * N') Nc
  let A : FinePhysicalOneCochain d L N' Nc :=
    singlePhysicalBondCochain
      (cmp96ConstraintPivotBond
        (d := d) (L := L) (N' := N') b)
      (((L : ℝ) ^ (d - 1)) • D b)
  have hbaseU :
      ∀ c : PhysicalBond d N', ∀ x ∈ blockOf L N' c.1,
        ‖cmp98UbarAmbientDeviationMatrix U c x 0‖ ≤ 1 / 3 :=
    cmp102PhysicalBackgroundBase_of_small
      hd hL U epsilon0 hepsilon0 hsmall hradius
  have hbase0 :
      ∀ c : PhysicalBond d N', ∀ x ∈ blockOf L N' c.1,
        ‖cmp98UbarAmbientDeviationMatrix U0 c x 0‖ ≤ 1 / 3 := by
    intro c x hx
    simp [U0]
  have hltU :
      ∀ c : PhysicalBond d N', ∀ x ∈ blockOf L N' c.1,
        ‖cmp98UbarAmbientDeviationMatrix U c x 0‖ < 1 :=
    fun c x hx => (hbaseU c x hx).trans_lt (by norm_num)
  have hlt0 :
      ∀ c : PhysicalBond d N', ∀ x ∈ blockOf L N' c.1,
        ‖cmp98UbarAmbientDeviationMatrix U0 c x 0‖ < 1 :=
    fun c x hx => (hbase0 c x hx).trans_lt (by norm_num)
  have hright :
      ‖cmp98Eq119NonlinearRightVariation U A b -
          cmp98Eq119NonlinearRightVariation U0 A b‖ ≤
        cmp102PhysicalRightVariationBackgroundBudget d L (1 / 3) epsilon0 *
          cmp98SourceFieldSupNorm A := by
    simpa only [U0] using
      norm_cmp98Eq119NonlinearRightVariation_sub_trivial_le_sourceScale
        U epsilon0 (1 / 3) hepsilon0 (by rfl) (by norm_num) hsmall A b
          (hbaseU b) (hbase0 b)
  have hsup :
      cmp98SourceFieldSupNorm A =
        (L : ℝ) ^ (d - 1) * ‖D b‖ := by
    simp only [A, cmp98SourceFieldSupNorm_singlePhysicalBondCochain,
      norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (L : ℝ) ^ (d - 1))]
  have hflat :
      cmp109PhysicalPivotResponseCLM U0 D b = D b := by
    exact congrArg (fun X : CoarsePhysicalOneCochain d N' Nc => X b)
      (cmp109PhysicalPivotResponseCLM_trivial_apply
        (d := d) (L := L) (N' := N') (Nc := Nc) hN' D)
  have hdiff :
      cmp109PhysicalPivotResponseCLM U D b - D b =
        cmp109PhysicalPivotResponseCLM U D b -
          cmp109PhysicalPivotResponseCLM U0 D b := by
    rw [hflat]
  unfold cmp109PhysicalPivotDefectCLM
  change ‖cmp109PhysicalPivotResponseCLM U D b - D b‖ ≤ _
  rw [hdiff,
    cmp109PhysicalPivotResponseCLM_apply_eq_diagonal U hN' hltU D b,
    cmp109PhysicalPivotResponseCLM_apply_eq_diagonal U0 hN' hlt0 D b]
  change
    ‖cmp109PhysicalLinearConstraint U A b -
        cmp109PhysicalLinearConstraint U0 A b‖ ≤ _
  rw [cmp109PhysicalLinearConstraint_eq_retractedRightVariation
      U A b (hltU b),
    cmp109PhysicalLinearConstraint_eq_retractedRightVariation
      U0 A b (hlt0 b),
    ← map_sub]
  calc
    ‖cmp98AmbientToLieCoordCLM Nc
        (cmp98Eq119NonlinearRightVariation U A b -
          cmp98Eq119NonlinearRightVariation U0 A b)‖
        ≤ ‖cmp98AmbientToLieCoordCLM Nc‖ *
            ‖cmp98Eq119NonlinearRightVariation U A b -
              cmp98Eq119NonlinearRightVariation U0 A b‖ :=
      (cmp98AmbientToLieCoordCLM Nc).le_opNorm _
    _ ≤ ‖cmp98AmbientToLieCoordCLM Nc‖ *
          (cmp102PhysicalRightVariationBackgroundBudget d L (1 / 3) epsilon0 *
            cmp98SourceFieldSupNorm A) :=
      mul_le_mul_of_nonneg_left hright (norm_nonneg _)
    _ = cmp109PhysicalPivotBackgroundBudget d L Nc epsilon0 * ‖D b‖ := by
      rw [hsup]
      unfold cmp109PhysicalPivotBackgroundBudget
      ring

/-- The genuine `L²` operator norm of the physical pivot defect is bounded by
the same volume-independent coefficient as every diagonal row. -/
theorem norm_cmp109PhysicalPivotDefectCLM_le_backgroundBudget
    (hd : 2 ≤ d) (hL : 2 ≤ L) (hN' : 2 ≤ N')
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (epsilon0 : ℝ) (hepsilon0 : 0 ≤ epsilon0)
    (hsmall : PhysicalWilsonSmallBackground U epsilon0)
    (hradius : cmp99SourceUbarFineDeviationRadius d L epsilon0 ≤ 1 / 3) :
    ‖cmp109PhysicalPivotDefectCLM U‖ ≤
      cmp109PhysicalPivotBackgroundBudget d L Nc epsilon0 := by
  let C := cmp109PhysicalPivotBackgroundBudget d L Nc epsilon0
  have hC : 0 ≤ C :=
    cmp109PhysicalPivotBackgroundBudget_nonneg hepsilon0
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro D
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hC (norm_nonneg D))).mp
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    ∑ b, ‖cmp109PhysicalPivotDefectCLM U D b‖ ^ 2
        ≤ ∑ b, (C * ‖D b‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hC (norm_nonneg (D b)))).mpr
          (norm_cmp109PhysicalPivotDefectCLM_apply_le_backgroundBudget
            hd hL hN' U epsilon0 hepsilon0 hsmall hradius D b)
    _ = C ^ 2 * ∑ b, ‖D b‖ ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]

/-- **CMP109 physical pivot contraction.**  Source small-background
regularity makes the literal pivot defect a strict contraction. -/
theorem norm_cmp109PhysicalPivotDefectCLM_lt_one_of_backgroundBudget
    (hd : 2 ≤ d) (hL : 2 ≤ L) (hN' : 2 ≤ N')
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (epsilon0 : ℝ) (hepsilon0 : 0 ≤ epsilon0)
    (hsmall : PhysicalWilsonSmallBackground U epsilon0)
    (hradius : cmp99SourceUbarFineDeviationRadius d L epsilon0 ≤ 1 / 3)
    (hbudget : cmp109PhysicalPivotBackgroundBudget d L Nc epsilon0 < 1) :
    ‖cmp109PhysicalPivotDefectCLM U‖ < 1 :=
  (norm_cmp109PhysicalPivotDefectCLM_le_backgroundBudget
    hd hL hN' U epsilon0 hepsilon0 hsmall hradius).trans_lt hbudget

end

end YangMills.RG
