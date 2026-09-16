/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Exact extraction of the physical Holder factor from the complete stabilized
CMP89 (2.49) integrand.  This is pointwise algebra only: no integral, tsum,
operator identity, owner metric, regional B0, window 15 or terminal field is
claimed here.
-/

import YangMills.RG.BalabanCMP89Eq249PhysicalFineHolderPhaseQuotient
import YangMills.RG.BalabanCMP89Eq249StabilizedComplexIntegrand

namespace YangMills.RG

noncomputable section

/-- The Holder power is a common scalar factor of every bare alias numerator.
The endpoint phases, derivative symbol and averaging amplitude are unchanged. -/
theorem cmp89Eq251ComplexBareAliasNumerator_eq_holderRpowInv_mul_zero_draft
    {d L j : ℕ} (alpha : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (derivMu : Fin d) (holder transport : Fin d → ℝ) :
    cmp89Eq251ComplexBareAliasNumerator d L j alpha z m derivMu
        holder transport =
      (((cmp89Eq251EuclideanNorm holder ^ alpha : ℝ) : ℂ)⁻¹) *
        cmp89Eq251ComplexBareAliasNumerator d L j 0 z m derivMu
          holder transport := by
  unfold cmp89Eq251ComplexBareAliasNumerator
  simp only [Real.rpow_zero, Nat.cast_one, one_div, div_eq_mul_inv]
  ring

/-- The same Holder factor pulls through the central/noncentral finite alias
assembly.  No alias phase or fine-symbol quotient is removed. -/
theorem cmp89Eq251ComplexStabilizedNumerator_eq_holderRpowInv_mul_zero_draft
    {d L j : ℕ} (mass alpha : ℝ) (z : Fin d → ℂ) (derivMu : Fin d)
    (holder transport : Fin d → ℝ) :
    cmp89Eq251ComplexStabilizedNumerator d L j mass alpha z derivMu
        holder transport =
      (((cmp89Eq251EuclideanNorm holder ^ alpha : ℝ) : ℂ)⁻¹) *
        cmp89Eq251ComplexStabilizedNumerator d L j mass 0 z derivMu
          holder transport := by
  rw [cmp89Eq251ComplexStabilizedNumerator,
    cmp89Eq251ComplexStabilizedNumerator]
  simp_rw [cmp89Eq251ComplexBareAliasNumerator_eq_holderRpowInv_mul_zero_draft]
  simp_rw [mul_div_assoc]
  rw [← Finset.mul_sum]
  ring

/-- The complete stabilized integrand at exponent `alpha` is the common
Holder scalar times its raw `alpha = 0` specialization. -/
theorem cmp89Eq251ComplexStabilizedIntegrand_eq_holderRpowInv_mul_zero_draft
    {d L j : ℕ} (mass a alpha : ℝ) (z : Fin d → ℂ) (derivMu : Fin d)
    (holder transport : Fin d → ℝ) :
    cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha z derivMu
        holder transport =
      (((cmp89Eq251EuclideanNorm holder ^ alpha : ℝ) : ℂ)⁻¹) *
        cmp89Eq251ComplexStabilizedIntegrand d L j mass a 0 z derivMu
          holder transport := by
  unfold cmp89Eq251ComplexStabilizedIntegrand
  rw [cmp89Eq251ComplexStabilizedNumerator_eq_holderRpowInv_mul_zero_draft]
  ring

/-- For a literal unit physical bond the common factor is exactly
`xi^(-alpha)`.  Derivative direction and bond direction remain independent. -/
theorem cmp89Eq251ComplexStabilizedIntegrand_physicalUnit_eq_xiRpowInv_mul_zero_draft
    {d L j : ℕ} {xi : ℝ} (hxi : 0 ≤ xi) (mass a alpha : ℝ)
    (z : Fin d → ℂ) (derivMu : Fin d) {holderU : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holderU)
    (transport : Fin d → ℝ) :
    cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha z derivMu
        (cmp89Eq249PhysicalFineLatticeDisplacement xi holderU) transport =
      (((xi ^ alpha : ℝ) : ℂ)⁻¹) *
        cmp89Eq251ComplexStabilizedIntegrand d L j mass a 0 z derivMu
          (cmp89Eq249PhysicalFineLatticeDisplacement xi holderU) transport := by
  rw [cmp89Eq251ComplexStabilizedIntegrand_eq_holderRpowInv_mul_zero_draft]
  rw [cmp89Eq251EuclideanNorm_physicalFineLatticeDisplacement_eq_draft hxi hunit]

end

end YangMills.RG
