/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq395Algebra
import YangMills.RG.BalabanCMP95PeriodicSquarePartitionSupportCardinality
import YangMills.RG.FinitePiLpTypedCutoff

/-!
# The square-partition operator identity used in CMP99 equation (3.95)

CMP99 uses the source normalization `sum_Pi h_Pi(x)^2 = 1` as an operator
identity.  This file proves that passage on the actual finite `L²` fields.
It is independent of the local covariance inverse, which remains the other
source-specific producer needed by (3.95).
-/

namespace YangMills.RG

noncomputable section

/-- Composition of two scalar multipliers is pointwise multiplication, with
the order of the two scalar functions retained literally. -/
theorem finitePiLpScalarMultiplier_comp
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h k : ι → ℝ) :
    (finitePiLpScalarMultiplier (g := g) h).comp
        (finitePiLpScalarMultiplier (g := g) k) =
      finitePiLpScalarMultiplier (g := g) (fun x => h x * k x) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro x
  simp [finitePiLpScalarMultiplier_apply, mul_smul]

/-- A pointwise support relation becomes the exact multiplier relation used
in each localized inverse term of (3.95). -/
theorem finitePiLpScalarMultiplier_comp_eq_of_pointwise_mul
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h chi : ι → ℝ) (hsupport : ∀ x, h x * chi x = h x) :
    (finitePiLpScalarMultiplier (g := g) h).comp
        (finitePiLpScalarMultiplier (g := g) chi) =
      finitePiLpScalarMultiplier (g := g) h := by
  rw [finitePiLpScalarMultiplier_comp]
  congr
  funext x
  exact hsupport x

/-- The centred CMP95 cutoff satisfies the literal source support identity
`h_Pi * chi_Pi = h_Pi` on every large block.  This is the exact pointwise
ingredient used in the first and third sums of CMP99 (3.95). -/
theorem cmp95SourcePeriodicCoarseSquarePartition_mul_piCharacteristic
    {Q : ℕ} [NeZero Q]
    (P : CMP95SourceSmoothPartitionProfile)
    (cell : FinBox 4 Q) (block : FinBox 4 (2 * Q)) :
    (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block *
        cmp99SourcePiCharacteristic cell block =
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block := by
  classical
  by_cases hsupport : cmp95SourcePeriodicCoarseCellSupport Q cell block
  · have hbase :=
      cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell
        cell block hsupport
    have hpi : block ∈ cmp99SourceTildePiLargeBlocks cell 0 := by
      rw [cmp99SourceTildePiLargeBlocks_zero]
      exact hbase
    simp [cmp99SourcePiCharacteristic, hpi]
  · rw [cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
      P Q cell block hsupport]
    simp

/-- The same smooth cutoff is supported inside the larger physical operator
region `tilde Pi^4`.  This is distinct from the source characteristic used in
the displayed correction terms. -/
theorem cmp95SourcePeriodicCoarseSquarePartition_mul_pi4Characteristic
    {Q : ℕ} [NeZero Q]
    (P : CMP95SourceSmoothPartitionProfile)
    (cell : FinBox 4 Q) (block : FinBox 4 (2 * Q)) :
    (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block *
        (if block ∈ cmp99SourceTildePiLargeBlocks cell 4 then 1 else 0) =
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block := by
  classical
  by_cases hsupport : cmp95SourcePeriodicCoarseCellSupport Q cell block
  · have hbase :=
      cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell
        cell block hsupport
    have hpi0 : block ∈ cmp99SourceTildePiLargeBlocks cell 0 := by
      rw [cmp99SourceTildePiLargeBlocks_zero]
      exact hbase
    have hpi4 : block ∈ cmp99SourceTildePiLargeBlocks cell 4 :=
      cmp99SourceTildePiLargeBlocks_mono cell (by omega) hpi0
    simp [hpi4]
  · rw [cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
      P Q cell block hsupport]
    simp

/-- Operator form of the source support identity on any finite coordinate
field whose sites carry a physical large-block coordinate. -/
theorem cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_characteristic
    {Q : ℕ} [NeZero Q]
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (P : CMP95SourceSmoothPartitionProfile)
    (cell : FinBox 4 Q) (blockOf : ι → FinBox 4 (2 * Q)) :
    (finitePiLpScalarMultiplier (g := g)
      (fun x => (cmp95SourcePeriodicCoarseSquarePartition P Q).value
        cell (blockOf x))).comp
      (finitePiLpScalarMultiplier (g := g)
        (fun x => cmp99SourcePiCharacteristic cell (blockOf x))) =
      finitePiLpScalarMultiplier (g := g)
        (fun x => (cmp95SourcePeriodicCoarseSquarePartition P Q).value
          cell (blockOf x)) := by
  apply finitePiLpScalarMultiplier_comp_eq_of_pointwise_mul
  intro x
  exact cmp95SourcePeriodicCoarseSquarePartition_mul_piCharacteristic
    P cell (blockOf x)

/-- Operator form of support inside `tilde Pi^4` on the ambient coarse block
field. -/
theorem cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_pi4
    {Q : ℕ} [NeZero Q]
    {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g]
    [FiniteDimensional ℝ g]
    (P : CMP95SourceSmoothPartitionProfile) (cell : FinBox 4 Q) :
    (finitePiLpScalarMultiplier (g := g)
      (fun block : FinBox 4 (2 * Q) =>
        (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block)).comp
      (finitePiLpScalarMultiplier (g := g)
        (fun block : FinBox 4 (2 * Q) =>
          if block ∈ cmp99SourceTildePiLargeBlocks cell 4 then 1 else 0)) =
      finitePiLpScalarMultiplier (g := g)
        (fun block : FinBox 4 (2 * Q) =>
          (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block) := by
  apply finitePiLpScalarMultiplier_comp_eq_of_pointwise_mul
  intro block
  exact cmp95SourcePeriodicCoarseSquarePartition_mul_pi4Characteristic
    P cell block

/-- The finite square partition of CMP99 resolves the identity on every
finite typed `L²` field after pulling block coordinates back along `blockOf`. -/
theorem sum_cmp99SourceSquarePartition_multiplier_sq_eq_id
    {Q : ℕ} [NeZero Q]
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (P : CMP99SourceSquarePartition Q)
    (blockOf : ι → FinBox 4 (2 * Q)) :
    (∑ cell : FinBox 4 Q,
      (finitePiLpScalarMultiplier (g := g)
        (fun x => P.value cell (blockOf x))).comp
      (finitePiLpScalarMultiplier (g := g)
        (fun x => P.value cell (blockOf x)))) =
      ContinuousLinearMap.id ℝ (FinitePiLpField ι g) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro x
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [finitePiLpScalarMultiplier_apply]
  simp_rw [smul_smul]
  rw [← Finset.sum_smul]
  have hsquare := P.square_sum (blockOf x)
  simp only [pow_two] at hsquare
  rw [hsquare]
  exact one_smul ℝ (f x)

end

end YangMills.RG
