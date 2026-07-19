/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99OneScaleRegionalPoincare
import YangMills.RG.BalabanCMP99SourcePhysicalGaugePrecision

/-!
# Physical one-scale coercivity for the CMP99 source precision

The regional Dirichlet Poincare estimate is converted to the printed lattice
spacing convention `D_U^eta = eta^{-1} D_U`.  Adding the literal one-step
source mass then gives an explicit coercivity constant, uniform in the
periodic volume and requiring no external Poincare hypothesis.
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- The literal one-step source average on a CMP99 Dirichlet region. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepQ
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc) :=
  cmp99SourceTransportedBlockAverageCLM
    (cmp99OmegaActiveGaugeRegion (M := M) Seq r)
    (cmp99SourceWeightedPhysicalTransport rho U)

/-- The one-step specialization of the printed physical source precision. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepGaugePrecision
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing a : ℝ) :=
  cmp99SourceGaugePrecision
    (cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing)
    (cmp99OmegaSourcePhysicalOneStepQ Seq r rho U) a

/-- Explicit spacing-adjusted one-scale Poincare constant. -/
noncomputable def cmp99OneScaleRegionalPhysicalPoincareConstant
    (M : ℕ) (spacing : ℝ) : ℝ :=
  cmp99OneScaleBlockPoincareConstant 4 M * max (spacing ^ 2) 1

theorem cmp99OneScaleRegionalPhysicalPoincareConstant_pos
    (spacing : ℝ) :
    0 < cmp99OneScaleRegionalPhysicalPoincareConstant M spacing := by
  unfold cmp99OneScaleRegionalPhysicalPoincareConstant
  exact mul_pos cmp99OneScaleBlockPoincareConstant_pos
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _))

/-- Exact conversion between the unscaled derivative and `D_U^eta`. -/
theorem norm_covariantD0_extendZero_eq_spacing_mul_physical
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (phi : CMP99OmegaDirichletZeroField
      (M := M) Seq r (SUNLieCoord Nc)) :
    ‖covariantD0CLM rho U
        (extendZeroZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi)‖ =
      spacing * ‖cmp99OmegaSourceCovariantD0CLM
        Seq r rho U spacing phi‖ := by
  change ‖covariantD0CLM rho U
        (extendZeroZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi)‖ =
    spacing * ‖spacing⁻¹ • covariantD0CLM rho U
      (extendZeroZeroCLM
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi)‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspacing)]
  field_simp

/-- Source-specific one-scale regional Poincare estimate in the printed
lattice-spacing normalization. -/
theorem norm_sq_le_cmp99OneScaleRegionalPhysicalPoincare
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (phi : CMP99OmegaDirichletZeroField
      (M := M) Seq r (SUNLieCoord Nc)) :
    ‖phi‖ ^ 2 ≤
      cmp99OneScaleRegionalPhysicalPoincareConstant M spacing *
        (inner ℝ phi
            (cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing phi) +
          ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U phi‖ ^ 2) := by
  have hreg := norm_sq_le_cmp99OneScaleRegionalPoincare
    (Omega := cmp99OmegaActiveGaugeRegion (M := M) Seq r)
    (cmp99OmegaActiveGaugeRegion_blockSaturated (M := M) Seq r)
    rho U phi
  have hD := norm_covariantD0_extendZero_eq_spacing_mul_physical
    Seq r rho U hspacing phi
  rw [hD] at hreg
  rw [inner_cmp99OmegaSourceCovariantLaplacian]
  change ‖phi‖ ^ 2 ≤
    cmp99OneScaleBlockPoincareConstant 4 M * max (spacing ^ 2) 1 *
      (‖cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing phi‖ ^ 2 +
        ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U phi‖ ^ 2)
  have hC : 0 ≤ cmp99OneScaleBlockPoincareConstant 4 M :=
    cmp99OneScaleBlockPoincareConstant_pos.le
  have hs : spacing ^ 2 ≤ max (spacing ^ 2) 1 := le_max_left _ _
  have hOne : 1 ≤ max (spacing ^ 2) 1 := le_max_right _ _
  have hD0 : 0 ≤ ‖cmp99OmegaSourceCovariantD0CLM
      Seq r rho U spacing phi‖ ^ 2 := sq_nonneg _
  have hQ0 : 0 ≤ ‖cmp99OmegaSourcePhysicalOneStepQ
      Seq r rho U phi‖ ^ 2 := sq_nonneg _
  calc
    ‖phi‖ ^ 2 ≤ cmp99OneScaleBlockPoincareConstant 4 M *
        ((spacing * ‖cmp99OmegaSourceCovariantD0CLM
          Seq r rho U spacing phi‖) ^ 2 +
          ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U phi‖ ^ 2) := hreg
    _ ≤ cmp99OneScaleBlockPoincareConstant 4 M * max (spacing ^ 2) 1 *
        (‖cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing phi‖ ^ 2 +
          ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U phi‖ ^ 2) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        (spacing * ‖cmp99OmegaSourceCovariantD0CLM
            Seq r rho U spacing phi‖) ^ 2 +
              ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U phi‖ ^ 2 =
            spacing ^ 2 * ‖cmp99OmegaSourceCovariantD0CLM
              Seq r rho U spacing phi‖ ^ 2 +
              1 * ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U phi‖ ^ 2 := by
                ring
        _ ≤ max (spacing ^ 2) 1 *
              ‖cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing phi‖ ^ 2 +
            max (spacing ^ 2) 1 *
              ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U phi‖ ^ 2 :=
          add_le_add
            (mul_le_mul_of_nonneg_right hs hD0)
            (mul_le_mul_of_nonneg_right hOne hQ0)
        _ = max (spacing ^ 2) 1 *
            (‖cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing phi‖ ^ 2 +
              ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U phi‖ ^ 2) := by
                ring

/-- The literal one-step CMP99 source precision is uniformly coercive, with
no external regional Poincare premise. -/
theorem coercive_cmp99OmegaSourcePhysicalOneStepGaugePrecision
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 ≤ a) :
    IsCoerciveCLM
      (cmp99OmegaSourcePhysicalOneStepGaugePrecision
        Seq r rho U spacing a)
      (min 1 a /
        cmp99OneScaleRegionalPhysicalPoincareConstant M spacing) := by
  intro phi
  simpa [cmp99OmegaSourcePhysicalOneStepGaugePrecision,
    cmp99SourceGaugePrecision] using
    (coercive_add_adjointMass_of_blockPoincare
      (cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing)
      (cmp99OmegaSourcePhysicalOneStepQ Seq r rho U)
      ha (cmp99OneScaleRegionalPhysicalPoincareConstant_pos spacing)
      (fun x => by
        rw [inner_cmp99OmegaSourceCovariantLaplacian]
        positivity)
      (norm_sq_le_cmp99OneScaleRegionalPhysicalPoincare
        Seq r rho U hspacing) phi)

end

end YangMills.RG
