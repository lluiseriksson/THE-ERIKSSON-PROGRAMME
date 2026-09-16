/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

/-
PRE-VALIDATION IMPORT CONTRACT.

The first import names the intended promoted H2b module.  It does not exist in
the tracked tree yet, so this integration draft is deliberately not a
compilable target until that leaf brick has been materialized.
-/
import YangMills.RG.BalabanCMP89Eq249PhysicalFineComplexHolderPhaseQuotient
import YangMills.RG.BalabanCMP89Eq251ComplexEndpointAmplitudeBound
import YangMills.RG.BalabanCMP89Eq251SignedContourPhase

/-!
# PRE-VALIDATION: physical fine Holder central branch

This H2d2 source is a static draft.  Its `.olean` has not been materialized
and none of its declarations has been compiler-verified.

It bounds the literal zero reciprocal-alias branch of CMP89 (2.49) on the
signed transport contour.  The physical Holder quotient is produced by H2b,
the transport phase gives the exact `ell^1` decay, and the remaining scaled
difference/averaging product is the already sealed central endpoint
amplitude.  The Brillouin-cube estimate `||p||_2 <= 2*pi` is proved here in
dimension four rather than hidden in a generic constant.

This module does not assemble the noncentral sum, multiply by the central
fine symbol, divide by the stabilized denominator, prove contour equality,
construct `B0`, attain window 15, discharge a terminal field or inhabit a
`TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- A four-dimensional momentum in the printed Brillouin cube has Euclidean
norm at most `2*pi`. -/
theorem cmp89Eq251EuclideanNorm_le_two_pi_of_mem_brillouin_draft
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq251EuclideanNorm p ≤ 2 * Real.pi := by
  have hterm : ∀ mu : Fin 4, p mu ^ 2 ≤ Real.pi ^ 2 := by
    intro mu
    have hbounds := abs_le.mp (hp mu)
    have hleft : 0 ≤ Real.pi - p mu := sub_nonneg.mpr hbounds.2
    have hright : 0 ≤ Real.pi + p mu := by linarith
    nlinarith [mul_nonneg hleft hright]
  have hsquare :
      cmp89Eq251MomentumSquare p ≤ (2 * Real.pi) ^ 2 := by
    rw [cmp89Eq251MomentumSquare]
    calc
      (∑ mu, p mu ^ 2) ≤ ∑ _mu : Fin 4, Real.pi ^ 2 :=
        Finset.sum_le_sum fun mu _ => hterm mu
      _ = 4 * Real.pi ^ 2 := by norm_num
      _ = (2 * Real.pi) ^ 2 := by ring
  rw [cmp89Eq251EuclideanNorm]
  have hsqrt :
      (Real.sqrt (cmp89Eq251MomentumSquare p)) ^ 2 =
        cmp89Eq251MomentumSquare p :=
    Real.sq_sqrt (cmp89Eq251MomentumSquare_nonneg p)
  have hsqrtNonneg :
      0 ≤ Real.sqrt (cmp89Eq251MomentumSquare p) := Real.sqrt_nonneg _
  nlinarith [Real.pi_pos]

/-- Explicit zero-alias H2d2 constant before the common stabilized
reciprocal is applied. -/
def cmp89Eq249ComplexPhysicalFineHolderCentralBranchBound_draft
    (rho alpha : ℝ) : ℝ :=
  2 * Real.exp (2 * rho) * ((2 * Real.pi) ^ alpha + rho) *
    cmp89Eq251ComplexCentralEndpointAmplitudeBound rho

/-- Literal zero reciprocal-alias branch with physical Holder spacing and
transport phase kept together. -/
def cmp89Eq249ComplexPhysicalFineHolderCentralBranch_draft
    (L j : ℕ) (alpha : ℝ) (z : Fin 4 → ℂ) (mu : Fin 4)
    (holderU : Fin 4 → ℤ) (transportDisplacement : Fin 4 → ℝ) : ℂ :=
  let xi : ℝ := ((L : ℝ) ^ j)⁻¹
  let physicalU := cmp89Eq249PhysicalFineLatticeDisplacement xi holderU
  ((Complex.exp (Complex.I * cmp89Eq251EntirePhase z physicalU) - 1) /
      ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)) *
    Complex.exp (Complex.I * cmp89Eq251EntirePhase z transportDisplacement) *
    cmp89Eq251ComplexCentralEndpointAmplitude L j z mu

/-- The literal zero-alias bare numerator is exactly H2d2's central branch. -/
theorem cmp89Eq251ComplexBareAliasNumerator_zero_eq_physicalFineHolderCentralBranch_draft
    {L j : ℕ} {alpha : ℝ} (z : Fin 4 → ℂ) (mu : Fin 4)
    (holderU : Fin 4 → ℤ) (transportDisplacement : Fin 4 → ℝ) :
    cmp89Eq251ComplexBareAliasNumerator 4 L j alpha z
        (cmp89Eq249ZeroAlias 4) mu
        (cmp89Eq249PhysicalFineLatticeDisplacement (((L : ℝ) ^ j)⁻¹) holderU)
        transportDisplacement =
      cmp89Eq249ComplexPhysicalFineHolderCentralBranch_draft
        L j alpha z mu holderU transportDisplacement := by
  rw [cmp89Eq249ComplexPhysicalFineHolderCentralBranch_draft,
    cmp89Eq251ComplexBareAliasNumerator,
    cmp89Eq251ComplexCentralEndpointAmplitude,
    cmp89Eq248EntireAliasMomentum_zero]
  ring

/-- H2d2: the zero reciprocal alias has the same exact signed transport
decay and one explicit, scale-uniform central Holder constant. -/
theorem
    norm_cmp89Eq249ComplexPhysicalFineHolderCentralBranch_signedContour_le_draft
    {L j : ℕ} [NeZero L] {rho alpha : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) (hrho : 0 ≤ rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {holderU : Fin 4 → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holderU)
    (transportDisplacement : Fin 4 → ℝ) (mu : Fin 4) :
    ‖cmp89Eq249ComplexPhysicalFineHolderCentralBranch_draft L j alpha
        (cmp89Eq251SignedContourMomentum rho p transportDisplacement) mu
        holderU transportDisplacement‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 transportDisplacement)) *
        cmp89Eq249ComplexPhysicalFineHolderCentralBranchBound_draft
          rho alpha := by
  let xi : ℝ := ((L : ℝ) ^ j)⁻¹
  let physicalU := cmp89Eq249PhysicalFineLatticeDisplacement xi holderU
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p transportDisplacement
  let decay : ℝ :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 transportDisplacement))
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p transportDisplacement nu
  have hphaseRaw :=
    norm_cmp89Eq249PhysicalFine_complexStripPhaseFactor_div_rpow_le_draft
      (L := L) (j := j) halpha0 halpha1 hrho hreal himag hunit
  have hphase :
      ‖(Complex.exp (Complex.I * cmp89Eq251EntirePhase z physicalU) - 1) /
          ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)‖ ≤
        2 * Real.exp (2 * rho) *
          (cmp89Eq251EuclideanNorm p ^ alpha + rho) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg
        (cmp89Eq251EuclideanNorm_nonneg physicalU) alpha)]
    simpa only [xi, physicalU, z] using hphaseRaw
  have hpNorm : cmp89Eq251EuclideanNorm p ≤ 2 * Real.pi :=
    cmp89Eq251EuclideanNorm_le_two_pi_of_mem_brillouin_draft hp
  have hpPow :
      cmp89Eq251EuclideanNorm p ^ alpha ≤ (2 * Real.pi) ^ alpha :=
    Real.rpow_le_rpow (cmp89Eq251EuclideanNorm_nonneg p) hpNorm halpha0
  have hphaseUniform :
      ‖(Complex.exp (Complex.I * cmp89Eq251EntirePhase z physicalU) - 1) /
          ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)‖ ≤
        2 * Real.exp (2 * rho) * ((2 * Real.pi) ^ alpha + rho) :=
    hphase.trans (mul_le_mul_of_nonneg_left
      (add_le_add_right hpPow rho) (by positivity))
  have htransport :
      ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z
          transportDisplacement)‖ = decay := by
    simpa [z, decay, cmp89Eq248EntireAliasMomentum_zero] using
      (norm_exp_I_cmp89Eq251EntireAliasPhase_signedContour
        rho p transportDisplacement (cmp89Eq249ZeroAlias 4))
  have hcentral :=
    norm_cmp89Eq251ComplexCentralEndpointAmplitude_le_bound
      (L := L) (j := j) hrho hp hreal himag mu
  have hdecay : 0 ≤ decay := (Real.exp_pos _).le
  have hphaseBoundNonneg :
      0 ≤ 2 * Real.exp (2 * rho) * ((2 * Real.pi) ^ alpha + rho) := by
    positivity
  rw [cmp89Eq249ComplexPhysicalFineHolderCentralBranch_draft,
    norm_mul, norm_mul, htransport,
    cmp89Eq249ComplexPhysicalFineHolderCentralBranchBound_draft]
  calc
    ‖(Complex.exp (Complex.I * cmp89Eq251EntirePhase z physicalU) - 1) /
          ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)‖ *
        decay * ‖cmp89Eq251ComplexCentralEndpointAmplitude L j z mu‖ ≤
      (2 * Real.exp (2 * rho) * ((2 * Real.pi) ^ alpha + rho)) *
        decay * cmp89Eq251ComplexCentralEndpointAmplitudeBound rho := by
      gcongr
    _ = decay *
        (2 * Real.exp (2 * rho) * ((2 * Real.pi) ^ alpha + rho) *
          cmp89Eq251ComplexCentralEndpointAmplitudeBound rho) := by ring

end

end YangMills.RG
