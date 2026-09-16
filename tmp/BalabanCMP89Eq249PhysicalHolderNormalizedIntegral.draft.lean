/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Literal physical Holder-normalized Brillouin integral and its exact reduction
to `xi^(-alpha)` times the raw `alpha = 0` endpoint-difference integral on a
unit physical bond.  This is an equality, not a bound; generated operators,
tsums, owner transport, regional B0, window 15 and terminal fields remain open.
-/

import YangMills.RG.BalabanCMP89Eq249PhysicalHolderAlphaFactorization
import YangMills.RG.BalabanCMP89Eq249MassUniformRealSliceRecombination

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Literal source-normalized complete stabilized integral at physical fine
spacing and general Holder exponent.  Unlike the historical raw integral,
this definition does not fix `alpha = 0`. -/
def cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_draft
    (L j : ℕ) [NeZero L] (mass a alpha : ℝ) (derivMu : Fin 4)
    (holderU transportU : Fin 4 → ℤ) : ℂ :=
  cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) derivMu
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) holderU)
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) transportU)

/-- At `alpha = 0` the literal Holder integral is definitionally the existing
raw source-normalized integral. -/
theorem cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_zero_draft
    (L j : ℕ) [NeZero L] (mass a : ℝ) (derivMu : Fin 4)
    (holderU transportU : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_draft
        L j mass a 0 derivMu holderU transportU =
      cmp89Eq249NormalizedFineLatticeStabilizedIntegral
        L j mass a derivMu holderU transportU := by
  rfl

/-- On a literal unit physical bond, Holder normalization contributes exactly
the common scalar `xi^(-alpha)` outside the raw endpoint-difference integral.
The equality is established before taking a norm. -/
theorem
    cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_eq_xiRpowInv_mul_raw_draft
    {L j : ℕ} [NeZero L] {mass a alpha : ℝ} (derivMu : Fin 4)
    {holderU : Fin 4 → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holderU)
    (transportU : Fin 4 → ℤ) :
    let xi := cmp89Eq249FineLatticeSpacing L j
    cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_draft
        L j mass a alpha derivMu holderU transportU =
      (((xi ^ alpha : ℝ) : ℂ)⁻¹) *
        cmp89Eq249NormalizedFineLatticeStabilizedIntegral
          L j mass a derivMu holderU transportU := by
  dsimp only
  let xi : ℝ := cmp89Eq249FineLatticeSpacing L j
  let holder : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi holderU
  let transport : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi transportU
  let c : ℂ := (((xi ^ alpha : ℝ) : ℂ)⁻¹)
  let productMeasure : Measure (Fin 4 → ℝ) :=
    Measure.pi fun _ : Fin 4 => volume.restrict (Set.uIoc 0 (2 * Real.pi))
  have hxi : 0 ≤ xi := (cmp89Eq249FineLatticeSpacing_pos L j).le
  have hintegral :
      (∫ x, cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
          derivMu holder transport ∂productMeasure) =
        c * ∫ x, cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a 0
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
          derivMu holder transport ∂productMeasure := by
    calc
      _ = ∫ x, c * cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a 0
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
          derivMu holder transport ∂productMeasure := by
            apply integral_congr_ae
            filter_upwards with x
            simpa [c, holder, xi] using
              (cmp89Eq251ComplexStabilizedIntegrand_physicalUnit_eq_xiRpowInv_mul_zero_draft
                (L := L) (j := j) hxi mass a alpha
                (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
                derivMu hunit transport)
      _ = c * ∫ x, cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a 0
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
          derivMu holder transport ∂productMeasure :=
            integral_const_mul c _
  unfold cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_draft
    cmp89Eq249NormalizedFineLatticeStabilizedIntegral
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
    cmp89Eq249FourDimensionalBrillouinMeasure
  simp only [holder, transport, xi, c] at hintegral ⊢
  rw [hintegral]
  ring

end

end YangMills.RG
