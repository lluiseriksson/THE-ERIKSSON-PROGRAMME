/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceZeroResidue
import YangMills.RG.BalabanCMP99SourceFineToCoarseCenteredOwnerDictionary
import YangMills.RG.BalabanCMP99PhysicalGreenZeroResidueBound

/-!
# Unit-F owner bound for the separated generated point-source Green

PRE-VALIDATION: source present, `.olean` not yet materialized, and results in
this module are not yet compiler-verified.

C3 identifies the generated `G Q'^*` point-source column with the literal
zero-residue physical Green series.  The physical zero-residue theorem bounds
that series in the centered endpoint weight, and C4a transports that weight
to the fine-block owner metric without identifying opposite antipodal signs.

The result is the exact Unit-F estimate at
`Kfine = L^(depth+1)` and `N = 2*(K*Q)`.  It retains the printed amplitude,
geometric residue factor and boundary factor.  It is not yet transported to
the CMP99 source-localization owner and is not regional `B0`, window-15
attainment or a terminal field.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Scalar Unit-F bound for the literal endpoint displacement of the
source-separated column.  The generated coefficient is internal and the
owner is the actual coarse source `y`. -/
theorem
    norm_tsum_cmp99SourceSeparatedGeneratedFlatPhysicalGreen_zeroResidue_le_owner
    (depth : ℕ) {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (y : FinBox 4 (2 * (K * Q))) :
    ‖∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          (L ^ (depth + 1)) 1 0
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              (L ^ (depth + 1)) x y mu) n.1‖ ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist
              (blockSite (L ^ (depth + 1)) (2 * (K * Q)) x) y : ℝ)) := by
  let Kfine : ℕ := L ^ (depth + 1)
  let N : ℕ := 2 * (K * Q)
  let a : ℝ :=
    cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0
  let u : Fin 4 → ℤ := fun mu =>
    -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement Kfine x y mu
  letI : NeZero Kfine := by
    dsimp [Kfine]
    infer_instance
  letI : NeZero N := by
    dsimp [N]
    infer_instance
  have hzero :=
    norm_tsum_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_zeroResidue_le_draft
      (K := Kfine) (N := N) (a := a) (rho := rho)
      (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
      hrho hamplitude hradius hwindow u
  have howner :=
    cmp89SignedLatticeL1ExponentialWeight_centered_neg_fineToCoarse_le_owner
      (M := Kfine) (N := N) hrho.le x y
  have hA :
      0 ≤ cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho := by
    have hpoint :=
      norm_cmp89Eq248PhysicalZeroMassGreen_le_signedLatticeWeight_draft
        (K := Kfine)
        (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
        hrho.le hamplitude hradius hwindow 0
    simpa using (le_trans (norm_nonneg _) hpoint)
  have hgeom : 0 ≤ (2 / (1 - Real.exp (-rho))) ^ 4 := by
    positivity
  change ‖∑' n : CMP99FlatIntegerResidueClass 4 N 0,
      cmp89Eq248CenteredGreenPhysicalFourierCoefficient
        Kfine 1 0 a u n.1‖ ≤ _
  calc
    ‖∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          Kfine 1 0 a u n.1‖ ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          cmp89SignedLatticeL1ExponentialWeight (rho / (Kfine : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (Kfine * N)
              u)) := hzero
    _ ≤ cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          (Real.exp (2 * rho) *
            Real.exp (-rho *
              (finBoxDist (blockSite Kfine N x) y : ℝ)))) := by
      gcongr
    _ = cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist (blockSite Kfine N x) y : ℝ)) := by
      ring

/-- Unit-F bound for the actual generated `G Q'^*` point-source column.  No
operator norm or supplied readout replaces the literal pointwise endpoint. -/
theorem
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_le_owner
    (hL : 2 ≤ L) (depth : ℕ)
    (y : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho) :
    ‖(((cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc)))
        (cmp99FlatComplexFibrePointSource y v)) x‖ ≤
      (cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist
              (blockSite (L ^ (depth + 1)) (2 * (K * Q)) x) y : ℝ))) *
        ‖v‖ := by
  rw [
    cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_eq_zeroResidue_smul
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth y v x hrho hamplitude hradius hwindow]
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right
    (norm_tsum_cmp99SourceSeparatedGeneratedFlatPhysicalGreen_zeroResidue_le_owner
      (L := L) (K := K) (Q := Q) depth hrho hamplitude hradius hwindow x y)
    (norm_nonneg v)

end

end YangMills.RG
