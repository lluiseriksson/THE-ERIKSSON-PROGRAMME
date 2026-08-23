/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceZeroResidue
import YangMills.RG.BalabanCMP99SourceFineToCoarseCenteredOwnerDictionary
import YangMills.RG.BalabanCMP99PhysicalGreenZeroResidueBound

/-!
# Unit-F owner bound for the literal source-flow point-source Green

PRE-VALIDATION: source present; `.olean` not yet materialized and the result
has not yet been verified by the compiler.

C3 identifies the literal source-flow `G Q'^*` point-source column with the
zero-residue physical Green series.  The physical zero-residue theorem bounds
that series in the centered endpoint weight, and C4a transports that weight
to the fine-block owner metric without identifying opposite antipodal signs.

The coefficient is exactly `cmp99SourceFlowFlatFullComplexA a L depth` and
its positivity is derived from `ha : 0 < a`.  No generated Poincare
coefficient, inverse, Green equality, readout or owner is accepted from the
caller.  This is not yet the CMP99 source-localization owner or a regional
`B0`, window-15 attainment, rows 23--24 or a terminal field.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Scalar Unit-F owner bound for the literal source-flow endpoint.  The
source coefficient and its positivity are internal, and the owner is the
actual coarse source `y`. -/
theorem
    norm_tsum_cmp99SourceSeparatedSourceFlowFlatPhysicalGreen_zeroResidue_le_owner
    (depth : ℕ) {a rho : ℝ} (ha : 0 < a)
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (y : FinBox 4 (2 * (K * Q))) :
    ‖∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          (L ^ (depth + 1)) 1 0
          (cmp99SourceFlowFlatFullComplexA a L depth)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              (L ^ (depth + 1)) x y mu) n.1‖ ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
          (cmp99SourceFlowFlatFullComplexA a L depth) rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist
              (blockSite (L ^ (depth + 1)) (2 * (K * Q)) x) y : ℝ)) := by
  let Kfine : ℕ := L ^ (depth + 1)
  let N : ℕ := 2 * (K * Q)
  let weightedA : ℝ := cmp99SourceFlowFlatFullComplexA a L depth
  let u : Fin 4 → ℤ := fun mu =>
    -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement Kfine x y mu
  letI : NeZero Kfine := by
    dsimp [Kfine]
    infer_instance
  letI : NeZero N := by
    dsimp [N]
    infer_instance
  have hweightedA : 0 < weightedA := by
    dsimp [weightedA, cmp99SourceFlowFlatFullComplexA]
    exact cmp99SourceMassParameter_pos ha
      (by exact_mod_cast (NeZero.pos L)) depth
  have hzero :=
    norm_tsum_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_zeroResidue_le_draft
      (K := Kfine) (N := N) (a := weightedA) (rho := rho)
      hweightedA.le hrho hamplitude hradius hwindow u
  have howner :=
    cmp89SignedLatticeL1ExponentialWeight_centered_neg_fineToCoarse_le_owner
      (M := Kfine) (N := N) hrho.le x y
  have hweightZero :
      cmp89SignedLatticeL1ExponentialWeight
          (rho / (Kfine : ℝ)) (0 : Fin 4 → ℤ) = 1 := by
    rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
    simp
  have hA :
      0 ≤ cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft weightedA rho := by
    have hpoint :=
      norm_cmp89Eq248PhysicalZeroMassGreen_le_signedLatticeWeight_draft
        hweightedA.le hrho.le hamplitude hradius hwindow 0
    simpa [hweightZero] using (le_trans (norm_nonneg _) hpoint)
  have hgeom : 0 ≤ (2 / (1 - Real.exp (-rho))) ^ 4 := by
    positivity
  change ‖∑' n : CMP99FlatIntegerResidueClass 4 N 0,
      cmp89Eq248CenteredGreenPhysicalFourierCoefficient
        Kfine 1 0 weightedA u n.1‖ ≤ _
  calc
    ‖∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          Kfine 1 0 weightedA u n.1‖ ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft weightedA rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          cmp89SignedLatticeL1ExponentialWeight (rho / (Kfine : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (Kfine * N)
              u)) := hzero
    _ ≤ cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft weightedA rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          (Real.exp (2 * rho) *
            Real.exp (-rho *
              (finBoxDist (blockSite Kfine N x) y : ℝ)))) := by
      gcongr
    _ = cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft weightedA rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist (blockSite Kfine N x) y : ℝ)) := by
      ring

/-- Unit-F owner bound for the literal source-flow `G Q'^*` point-source
column.  The endpoint and its owner remain pointwise and physical. -/
theorem
    norm_cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_le_owner
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (y : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho) :
    ‖(((cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc)))
        (cmp99FlatComplexFibrePointSource y v)) x‖ ≤
      (cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
          (cmp99SourceFlowFlatFullComplexA a L depth) rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist
              (blockSite (L ^ (depth + 1)) (2 * (K * Q)) x) y : ℝ))) *
        ‖v‖ := by
  rw [
    cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_eq_zeroResidue_smul
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth ha y v x hrho hamplitude hradius hwindow]
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right
    (norm_tsum_cmp99SourceSeparatedSourceFlowFlatPhysicalGreen_zeroResidue_le_owner
      (L := L) (K := K) (Q := Q) depth ha hrho hamplitude hradius hwindow x y)
    (norm_nonneg v)

end

end YangMills.RG
