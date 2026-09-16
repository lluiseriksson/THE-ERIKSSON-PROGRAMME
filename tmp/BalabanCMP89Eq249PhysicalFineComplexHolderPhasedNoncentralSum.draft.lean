/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

/-
PRE-VALIDATION IMPORT CONTRACT.

The first three imports name intended promoted H2b/H2c modules.  They do not
exist in the tracked tree yet, so this integration draft is deliberately not a
compilable target until those leaf bricks have been materialized.
-/
import YangMills.RG.BalabanCMP89Eq249PhysicalFineComplexHolderPhaseQuotient
import YangMills.RG.BalabanCMP89Eq249ComplexHolderRadialRedistribution
import YangMills.RG.BalabanCMP89Eq249ComplexHolderAliasSummation
import YangMills.RG.BalabanCMP89Eq251SignedContourPhase

/-!
# PRE-VALIDATION: physical fine Holder phased noncentral sum

This H2d1 source is a static draft.  Its `.olean` has not been materialized
and none of its declarations has been compiler-verified.

It inserts the literal physical Holder quotient and the literal transport
phase in every noncentral reciprocal-alias summand of CMP89 (2.49).  On the
signed contour based at the transport displacement, every alias has the same
exact transport decay.  The physical H2b quotient and radial redistribution
then land on the single general-`alpha` source weight summed by H2c.

No reciprocal-alias phase is cancelled at fine spacing, no alias-cardinality
factor is introduced, and the endpoint transport exponential is never
replaced by a free caller-supplied bound.  This module does not assemble the
central branch, divide by the common stabilized denominator, prove contour
equality, construct `B0`, attain window 15, discharge a terminal field or
inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Literal noncentral part of the physical fine-lattice Holder numerator.
The Holder and transport phases remain in the same alias summand. -/
def cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_draft
    (L j : ℕ) (mass alpha : ℝ) (z : Fin 4 → ℂ) (mu : Fin 4)
    (holderU : Fin 4 → ℤ) (transportDisplacement : Fin 4 → ℝ) : ℂ :=
  let xi : ℝ := ((L : ℝ) ^ j)⁻¹
  let physicalU := cmp89Eq249PhysicalFineLatticeDisplacement xi holderU
  ∑ m ∈ (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
      (cmp89Eq249ZeroAlias 4),
    ((Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m) physicalU) - 1) /
        ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)) *
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m) transportDisplacement) *
      (cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹)
          (-(cmp89Eq248EntireAliasMomentum z m mu)) *
        cmp89Eq245EntireAverageAmplitude 4 (L ^ j)
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m))

/-- H2d1: the complete noncentral physical Holder sum has the exact signed
transport decay and one general-`alpha` alias-series constant. -/
theorem
    norm_cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_signedContour_le_draft
    {L j : ℕ} [NeZero L] {mass rho alpha : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (halphaStrict : alpha < 1) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {holderU : Fin 4 → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holderU)
    (transportDisplacement : Fin 4 → ℝ)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) :
    ‖cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_draft
        L j mass alpha
        (cmp89Eq251SignedContourMomentum rho p transportDisplacement) mu
        holderU transportDisplacement‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 transportDisplacement)) *
        cmp89Eq249ComplexHolderNoncentralAliasSumBound_draft rho alpha := by
  let N : ℕ := L ^ j
  let aliases := cmp89Eq245CenteredAliasVectors 4 N
  let zeroAlias := cmp89Eq249ZeroAlias 4
  let xi : ℝ := ((L : ℝ) ^ j)⁻¹
  let physicalU := cmp89Eq249PhysicalFineLatticeDisplacement xi holderU
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p transportDisplacement
  let q : (Fin 4 → ℤ) → Fin 4 → ℝ := fun m nu =>
    p nu + 2 * Real.pi * (m nu : ℝ)
  let quotient : (Fin 4 → ℤ) → ℂ := fun m =>
    cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹)
          (-(cmp89Eq248EntireAliasMomentum z m mu)) *
        cmp89Eq245EntireAverageAmplitude 4 N
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m)
  let weight : (Fin 4 → ℤ) → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 alpha) m
  let decay : ℝ :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 transportDisplacement))
  have hN : 0 < N :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p transportDisplacement nu
  have hdecay : 0 ≤ decay := (Real.exp_pos _).le
  have hconstant :
      0 ≤ cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha := by
    rw [cmp89Eq249ComplexHolderNoncentralRadialConstant_draft,
      cmp89Eq251ComplexNoncentralEndpointRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hpointwise :
      ∀ m ∈ aliases.erase zeroAlias,
        ‖((Complex.exp (Complex.I * cmp89Eq251EntirePhase
              (cmp89Eq248EntireAliasMomentum z m) physicalU) - 1) /
            ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)) *
          Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m) transportDisplacement) *
          quotient m‖ ≤
        decay *
          (cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha *
            weight m) := by
    intro m hm
    have hmParts := Finset.mem_erase.mp hm
    have hm0 : m ≠ 0 := by
      simpa only [zeroAlias, cmp89Eq249ZeroAlias] using hmParts.1
    have hphaseRaw :=
      norm_cmp89Eq249PhysicalFine_complexStripPhaseFactor_div_rpow_le_draft
        (L := L) (j := j) halpha0 halpha1 hrho
        (z := cmp89Eq248EntireAliasMomentum z m) (q := q m)
        (fun nu => by
          simp [z, q, cmp89Eq248EntireAliasMomentum,
            cmp89Eq245AliasShift])
        (fun nu => by
          simpa [z, cmp89Eq248EntireAliasMomentum,
            cmp89Eq245AliasShift] using himag nu)
        hunit
    have hphase :
        ‖(Complex.exp (Complex.I * cmp89Eq251EntirePhase
              (cmp89Eq248EntireAliasMomentum z m) physicalU) - 1) /
            ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)‖ ≤
          2 * Real.exp (2 * rho) *
            (cmp89Eq251EuclideanNorm (q m) ^ alpha + rho) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg
          (cmp89Eq251EuclideanNorm_nonneg physicalU) alpha)]
      simpa only [xi, physicalU, q] using hphaseRaw
    have htransport :
        ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m) transportDisplacement)‖ =
          decay := by
      simpa [z, decay] using
        (norm_exp_I_cmp89Eq251EntireAliasPhase_signedContour
          rho p transportDisplacement m)
    have hquotient :=
      norm_cmp89Eq251ComplexNoncentralEndpointQuotient_le_radialWeight
        (mass := mass) hN hrho hradius hmParts.2 hm0 hp hreal himag
        hamplitude mu
    have hradial :=
      cmp89Eq249_complexHolderPhase_mul_endpointRadial_le_sourceWeight_draft
        halpha0 halpha1 hrho hm0 hp
    rw [norm_mul, norm_mul, htransport]
    calc
      ‖(Complex.exp (Complex.I * cmp89Eq251EntirePhase
              (cmp89Eq248EntireAliasMomentum z m) physicalU) - 1) /
            ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)‖ *
          decay * ‖quotient m‖ ≤
        (2 * Real.exp (2 * rho) *
            (cmp89Eq251EuclideanNorm (q m) ^ alpha + rho)) *
          decay *
            (cmp89Eq251ComplexNoncentralEndpointRadialConstant rho *
              (cmp89Eq251EuclideanNorm (q m) ^ ((0 : ℝ) - 1) *
                cmp89Eq251MultidimensionalAliasWeight 1 m)) := by
          gcongr
          simpa only [quotient, q, z, N, Nat.cast_pow] using hquotient
      _ = decay *
          ((2 * Real.exp (2 * rho) *
              (cmp89Eq251EuclideanNorm (q m) ^ alpha + rho)) *
            (cmp89Eq251ComplexNoncentralEndpointRadialConstant rho *
              (cmp89Eq251EuclideanNorm (q m) ^ ((0 : ℝ) - 1) *
                cmp89Eq251MultidimensionalAliasWeight 1 m))) := by ring
      _ ≤ decay *
          (cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha *
            weight m) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [q, weight] using hradial) hdecay
  have heraseWeight :
      (∑ m ∈ aliases.erase zeroAlias, weight m) ≤
        cmp89Eq251CenteredMultidimensionalAliasSum 4 N
          (cmp89Eq251AliasSeriesExponent 4 alpha) := by
    rw [cmp89Eq251CenteredMultidimensionalAliasSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset zeroAlias aliases)
      (fun m _ _ =>
        cmp89Eq251MultidimensionalAliasWeight_nonneg
          (cmp89Eq251AliasSeriesExponent 4 alpha) m)
  have hseries :=
    cmp89Eq249_complexHolderCenteredAliasSum_le_uniform_draft
      N hrho halphaStrict
  rw [cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_draft]
  change ‖∑ m ∈ aliases.erase zeroAlias,
      ((Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m) physicalU) - 1) /
          ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)) *
        Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m) transportDisplacement) *
        quotient m‖ ≤ _
  calc
    ‖∑ m ∈ aliases.erase zeroAlias,
        ((Complex.exp (Complex.I * cmp89Eq251EntirePhase
              (cmp89Eq248EntireAliasMomentum z m) physicalU) - 1) /
            ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)) *
          Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m) transportDisplacement) *
          quotient m‖ ≤
      ∑ m ∈ aliases.erase zeroAlias,
        ‖((Complex.exp (Complex.I * cmp89Eq251EntirePhase
              (cmp89Eq248EntireAliasMomentum z m) physicalU) - 1) /
            ((cmp89Eq251EuclideanNorm physicalU ^ alpha : ℝ) : ℂ)) *
          Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m) transportDisplacement) *
          quotient m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ aliases.erase zeroAlias,
        decay *
          (cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha *
            weight m) := Finset.sum_le_sum hpointwise
    _ = decay *
        (cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha *
          ∑ m ∈ aliases.erase zeroAlias, weight m) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ decay *
        (cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha *
          cmp89Eq251CenteredMultidimensionalAliasSum 4 N
            (cmp89Eq251AliasSeriesExponent 4 alpha)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left heraseWeight hconstant) hdecay
    _ ≤ decay *
        cmp89Eq249ComplexHolderNoncentralAliasSumBound_draft rho alpha := by
      exact mul_le_mul_of_nonneg_left hseries hdecay

end

end YangMills.RG
