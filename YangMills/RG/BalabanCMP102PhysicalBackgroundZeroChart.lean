/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalBackgroundCorrectionScalarFixedPoint

/-!
# A common zero-field chart for CMP102 fixed-point comparison

The scalar data at a field `A` control every shifted field in its correction
ball by one source envelope.  Since that envelope is nonnegative, the same
data also construct a chart for the zero field with exactly the same local
and relative radii.  This is the missing typed input for comparing the
physical fixed point at `A` with the normalized zero solution.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

omit [NeZero Nc] in
/-- The finite source sup norm is normalized on the zero cochain. -/
@[simp] theorem cmp98SourceFieldSupNorm_zero :
    cmp98SourceFieldSupNorm
      (0 : PhysicalGaugeOneCochain d (L * N') Nc) = 0 := by
  unfold cmp98SourceFieldSupNorm
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨b, _hb, rfl⟩
    simp
  · exact (norm_nonneg
      ((0 : PhysicalGaugeOneCochain d (L * N') Nc)
        (Classical.choice inferInstance))).trans
        (Finset.le_max' _ _ (by simp))

namespace CMP102PhysicalBackgroundCorrectionScalarData

variable
    {U : PhysicalGaugeBackground d (L * N') Nc}
    {a CP ε : ℝ} {ha : 0 < a}
    {hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP}
    {hε : 0 ≤ ε} {hsmall : PhysicalWilsonSmallBackground U ε}
    {hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP}
    {A : PhysicalGaugeOneCochain d (L * N') Nc}
    {ρ radius r s : ℝ}
    (S : CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A ρ radius r s)

/-- The common source envelope is nonnegative. -/
theorem backgroundBallSourceEnvelope_nonneg
    (S' : CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A ρ radius r s) :
    0 ≤ cmp102PhysicalBackgroundBallSourceEnvelope
      U ha hP hε hsmall hbudget A ρ := by
  unfold cmp102PhysicalBackgroundBallSourceEnvelope
  exact add_nonneg
    (cmp98SourceFieldSupNorm_nonneg A)
    (mul_nonneg (norm_nonneg _) S'.rho_nonneg)

/-- The scalar data for `A` canonically provide a chart at the zero field,
with the same radii `r` and `s`. -/
noncomputable def zeroChartBudget :
    CMP102PhysicalNonlinearChartBudget
      U (0 : PhysicalGaugeOneCochain d (L * N') Nc) :=
  cmp102PhysicalNonlinearChartBudget_of_envelope
    U 0
    (cmp102PhysicalBackgroundBallSourceEnvelope
      U ha hP hε hsmall hbudget A ρ)
    radius r s
    (by simpa using backgroundBallSourceEnvelope_nonneg S)
    S.one_lt_radius S.r_nonneg S.r_lt_one S.s_lt_one
    S.r_noWinding S.s_noWinding
    (cmp102PhysicalBackgroundBase_of_small
      S.dimension_two_le S.blockScale_two_le U ε hε hsmall
        S.background_radius)
    S.line_small S.local_envelope S.relative_envelope

/-- The common zero chart has literally the source local radius. -/
@[simp] theorem zeroChartBudget_localRadius :
    S.zeroChartBudget.localNoWinding.δ = r := rfl

/-- The common zero chart has literally the source relative radius. -/
@[simp] theorem zeroChartBudget_relativeRadius :
    S.zeroChartBudget.relativeNoWinding.δ = s := rfl

end CMP102PhysicalBackgroundCorrectionScalarData

end

end YangMills.RG
