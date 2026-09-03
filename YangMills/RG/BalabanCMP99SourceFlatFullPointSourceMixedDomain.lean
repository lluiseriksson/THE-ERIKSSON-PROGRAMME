/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceSolutionDomain
import YangMills.RG.BalabanCMP99CenteredTorusPhysicalGreenSampleTransport

/-!
# PRE-VALIDATION: mixed centered/physical domains for the full Eq. (2.46) solver

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

This module isolates the only non-periodic ingredient needed while
changing the four coarse-momentum coordinates one at a time: the central
opposite-momentum averaging pair.  Each coordinate is chosen from either the
centered representative or the literal physical representative.  The proof
uses factorwise nonvanishing extracted from the two endpoint products; it
does not declare the central pair periodic.

This module does not prove CMP89 (2.42), produce `B0` or `delta0`, attain
window 15, move `20/41`, or construct a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Coordinatewise mixture of the centered and literal physical coarse
representatives. -/
def cmp99SourceFlatFullPointSourceMixedMomentum
    {N' : ℕ} [NeZero N'] (ell : FinBox 4 N')
    (physicalCoordinate : Fin 4 → Bool) : Fin 4 → ℂ :=
  fun mu =>
    if physicalCoordinate mu then
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell mu
    else
      (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ)

/-- At each coordinate the centered representative is either already the
literal physical representative or is obtained from it by adding exactly
one positive physical period.  No larger carry is possible because the two
representatives lie respectively in `[-pi,pi]` and `(-2*pi,0]`. -/
theorem cmp99SourceFlatQprime_centered_eq_physical_or_add_period
    {N' : ℕ} [NeZero N'] (ell : FinBox 4 N') (mu : Fin 4) :
    (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ) =
        cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell mu ∨
      (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ) =
        cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell mu +
          (2 * Real.pi : ℂ) := by
  rcases
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_eq_centered_add_intPeriods
        ell with
    ⟨w, hw⟩
  have hwCoord := congrFun hw mu
  have hwReal := congrArg Complex.re hwCoord
  have hN : 0 < (N' : ℝ) := by exact_mod_cast NeZero.pos N'
  have hk0 : 0 ≤ ((ell mu).val : ℝ) := by positivity
  have hkN : ((ell mu).val : ℝ) < (N' : ℝ) := by
    exact_mod_cast (ell mu).isLt
  have hcenteredAbs :=
    abs_cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_le_pi ell mu
  rcases abs_le.mp hcenteredAbs with
    ⟨hcenteredLower, hcenteredUpper⟩
  have hphysicalLe :
      - (2 * Real.pi * ((ell mu).val : ℝ) / (N' : ℝ)) ≤ 0 := by
    positivity
  have hphysicalGt :
      -2 * Real.pi <
        - (2 * Real.pi * ((ell mu).val : ℝ) / (N' : ℝ)) := by
    have hratio : ((ell mu).val : ℝ) / (N' : ℝ) < 1 :=
      (div_lt_one hN).2 hkN
    nlinarith [Real.pi_pos]
  have hwReal' :
      - (2 * Real.pi * ((ell mu).val : ℝ) / (N' : ℝ)) =
        cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu +
          (w mu : ℝ) * (2 * Real.pi) := by
    simpa [cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum] using hwReal
  have hwLtOne : (w mu : ℝ) < 1 := by
    nlinarith [Real.pi_pos]
  have hwGtNegTwo : (-2 : ℝ) < (w mu : ℝ) := by
    nlinarith [Real.pi_pos]
  have hwIntLtOne : w mu < 1 := by exact_mod_cast hwLtOne
  have hwIntGtNegTwo : (-2 : ℤ) < w mu := by exact_mod_cast hwGtNegTwo
  have hwCases : w mu = 0 ∨ w mu = -1 := by omega
  rcases hwCases with hzero | hneg
  · left
    rw [hwCoord, hzero]
    simp
  · right
    rw [hwCoord, hneg]
    push_cast
    ring

/-- The central average pair remains nonzero for every coordinatewise
mixture of the two endpoint representatives.  This is a factor theorem, not
a periodicity assertion for the pair. -/
theorem cmp89Eq249CentralEntireAveragePair_mixedCoarse_ne_zero
    {M N' : ℕ} [NeZero M] [NeZero N'] {rho : ℝ}
    (hrho : 0 ≤ rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (ell : FinBox 4 N') (physicalCoordinate : Fin 4 → Bool) :
    cmp89Eq249CentralEntireAveragePair 4 M 1
      (cmp99SourceFlatFullPointSourceMixedMomentum ell physicalCoordinate) ≠ 0 := by
  let centered : Fin 4 → ℂ := fun mu =>
    (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ)
  let physical : Fin 4 → ℂ :=
    cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  have hcentered :
      cmp89Eq249CentralEntireAveragePair 4 M 1 centered ≠ 0 := by
    let p := cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell
    exact cmp89Eq249CentralEntireAveragePair_ne_zero
      hrho hpairWindow
      (fun mu => abs_cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_le_pi ell mu)
      (by intro mu; rfl)
      (by intro mu; simpa using hrho)
  have hphysical :
      cmp89Eq249CentralEntireAveragePair 4 M 1 physical ≠ 0 := by
    exact cmp89Eq249CentralEntireAveragePair_physicalCoarse_ne_zero ell
  have hcenteredPos : cmp89Eq245EntireAverageAmplitude 4 M centered ≠ 0 := by
    intro hz
    apply hcentered
    simp [cmp89Eq249CentralEntireAveragePair, pow_one,
      cmp89Eq245EntireAveragePair, hz]
  have hcenteredNeg : cmp89Eq245EntireAverageAmplitude 4 M (-centered) ≠ 0 := by
    intro hz
    apply hcentered
    simp [cmp89Eq249CentralEntireAveragePair, pow_one,
      cmp89Eq245EntireAveragePair, hz]
  have hphysicalPos : cmp89Eq245EntireAverageAmplitude 4 M physical ≠ 0 := by
    intro hz
    apply hphysical
    simp [cmp89Eq249CentralEntireAveragePair, pow_one,
      cmp89Eq245EntireAveragePair, hz]
  have hphysicalNeg : cmp89Eq245EntireAverageAmplitude 4 M (-physical) ≠ 0 := by
    intro hz
    apply hphysical
    simp [cmp89Eq249CentralEntireAveragePair, pow_one,
      cmp89Eq245EntireAveragePair, hz]
  have hmixedPos :
      cmp89Eq245EntireAverageAmplitude 4 M
        (cmp99SourceFlatFullPointSourceMixedMomentum ell physicalCoordinate) ≠ 0 := by
    rw [cmp89Eq245EntireAverageAmplitude]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro mu hmu
    by_cases hchoice : physicalCoordinate mu = true
    · have hfactor := (Finset.prod_ne_zero_iff.mp (by
          simpa [cmp89Eq245EntireAverageAmplitude] using hphysicalPos)) mu
          (Finset.mem_univ mu)
      simpa [cmp99SourceFlatFullPointSourceMixedMomentum, physical,
        hchoice] using hfactor
    · have hfalse : physicalCoordinate mu = false := Bool.eq_false_of_not_eq_true hchoice
      have hfactor := (Finset.prod_ne_zero_iff.mp (by
          simpa [cmp89Eq245EntireAverageAmplitude] using hcenteredPos)) mu
          (Finset.mem_univ mu)
      simpa [cmp99SourceFlatFullPointSourceMixedMomentum, centered,
        hfalse] using hfactor
  have hmixedNeg :
      cmp89Eq245EntireAverageAmplitude 4 M
        (-cmp99SourceFlatFullPointSourceMixedMomentum ell physicalCoordinate) ≠ 0 := by
    rw [cmp89Eq245EntireAverageAmplitude]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro mu hmu
    by_cases hchoice : physicalCoordinate mu = true
    · have hfactor := (Finset.prod_ne_zero_iff.mp (by
          simpa [cmp89Eq245EntireAverageAmplitude] using hphysicalNeg)) mu
          (Finset.mem_univ mu)
      simpa [cmp99SourceFlatFullPointSourceMixedMomentum, physical,
        hchoice] using hfactor
    · have hfalse : physicalCoordinate mu = false := Bool.eq_false_of_not_eq_true hchoice
      have hfactor := (Finset.prod_ne_zero_iff.mp (by
          simpa [cmp89Eq245EntireAverageAmplitude] using hcenteredNeg)) mu
          (Finset.mem_univ mu)
      simpa [cmp99SourceFlatFullPointSourceMixedMomentum, centered,
        hfalse] using hfactor
  simpa [cmp89Eq249CentralEntireAveragePair, pow_one,
    cmp89Eq245EntireAveragePair] using mul_ne_zero hmixedPos hmixedNeg

/-- Every mixed representative on a nonzero coarse fibre belongs to the
complete full-solver domain.  The fine fibre and multiplied denominator are
transported from the centered endpoint by their proved integer-period
theorems.  The central row is supplied by the factorwise theorem above; the
stabilized denominator itself is not declared periodic. -/
theorem cmp99SourceFlatFullPointSourceSolutionDomain_mixed
    {M N' : ℕ} [NeZero M] [NeZero N'] {a rho : ℝ}
    (ha : 0 < a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    {ell : FinBox 4 N'} (hell : ell ≠ 0)
    (physicalCoordinate : Fin 4 → Bool) :
    CMP89Eq246FullSolutionDomain 4 M 1 0 a
      (cmp99SourceFlatFullPointSourceMixedMomentum ell physicalCoordinate) := by
  let centered : Fin 4 → ℂ := fun mu =>
    (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ)
  let mixed :=
    cmp99SourceFlatFullPointSourceMixedMomentum ell physicalCoordinate
  rcases
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_eq_centered_add_intPeriods
        ell with
    ⟨w, hw⟩
  let mixedPeriods : Fin 4 → ℤ := fun mu =>
    if physicalCoordinate mu then w mu else 0
  have hmixed : mixed = fun mu =>
      centered mu + (mixedPeriods mu : ℂ) * (2 * Real.pi : ℂ) := by
    funext mu
    by_cases hchoice : physicalCoordinate mu = true
    · have hcoord := congrFun hw mu
      simpa [mixed, centered, mixedPeriods,
        cmp99SourceFlatFullPointSourceMixedMomentum, hchoice] using hcoord
    · have hfalse : physicalCoordinate mu = false :=
        Bool.eq_false_of_not_eq_true hchoice
      simp [mixed, centered, mixedPeriods,
        cmp99SourceFlatFullPointSourceMixedMomentum, hfalse]
  have hcenteredFine :
      ∀ m : {m : Fin 4 → ℤ //
          m ∈ cmp89Eq245CenteredAliasVectors 4 M},
        cmp89Eq245EntireScaledLaplacianSymbol 4 ((M : ℝ)⁻¹) 0
            (cmp89Eq248EntireAliasMomentum centered m.1) ≠ 0 := by
    simpa only [centered] using
      (cmp89Eq245EntireAliasFibre_massZero_ne_zero_centered
        (d := 4) (M := M) (N' := N') hell)
  have hmixedFine :
      ∀ m : {m : Fin 4 → ℤ //
          m ∈ cmp89Eq245CenteredAliasVectors 4 M},
        cmp89Eq245EntireScaledLaplacianSymbol 4 ((M : ℝ)⁻¹) 0
            (cmp89Eq248EntireAliasMomentum mixed m.1) ≠ 0 := by
    rw [hmixed]
    exact
      (cmp89Eq245EntireAliasFibreNonvanishing_add_intPeriods_iff
        (d := 4) (M := M) 0 centered mixedPeriods).2 hcenteredFine
  have hfine : ∀ m : CMP89Eq246AliasIndex 4 M 1,
      m ≠ cmp89Eq249CentralAliasIndex 4 M 1 →
        cmp89Eq246EntireAliasFineSymbol 4 M 1 0 mixed m ≠ 0 := by
    intro m hm
    let m' : {m : Fin 4 → ℤ //
        m ∈ cmp89Eq245CenteredAliasVectors 4 M} :=
      ⟨m.1, by simpa only [pow_one] using m.2⟩
    simpa [cmp89Eq246EntireAliasFineSymbol, pow_one, m'] using
      hmixedFine m'
  have hcentralFine :
      cmp89Eq249CentralEntireFineSymbol 4 M 1 0 mixed ≠ 0 := by
    let m0 : {m : Fin 4 → ℤ //
        m ∈ cmp89Eq245CenteredAliasVectors 4 M} :=
      ⟨cmp89Eq249ZeroAlias 4,
        by simpa only [pow_one] using cmp89Eq249ZeroAlias_mem 4 M 1⟩
    simpa [cmp89Eq249CentralEntireFineSymbol,
      cmp89Eq248EntireAliasMomentum_zero, m0] using hmixedFine m0
  rcases cmp99MassZeroDisplayedGreenDomain_centered
      (K := M) (N' := N') ha hell with
    ⟨hunitCentered, hreducedCentered, hdisplayedFineCentered⟩
  have hfullCentered :
      cmp89Eq249ComplexFullAliasDenominator 4 M 1 0 a centered ≠ 0 := by
    rw [cmp89Eq249ComplexFullAliasDenominator]
    exact mul_ne_zero hreducedCentered hunitCentered
  have hfullMixed :
      cmp89Eq249ComplexFullAliasDenominator 4 M 1 0 a mixed ≠ 0 := by
    rw [hmixed, cmp89Eq249ComplexFullAliasDenominator_add_intPeriods]
    exact hfullCentered
  have hreducedMixed :
      cmp89Eq247ComplexReducedAliasDenominator 4 M 1 0 a mixed ≠ 0 := by
    intro hz
    apply hfullMixed
    simp [cmp89Eq249ComplexFullAliasDenominator, hz]
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 M 1 0 a mixed ≠ 0 := by
    rw [← cmp89Eq249CentralFine_mul_reduced_eq_stabilized
      4 M 1 0 a mixed hcentralFine]
    exact mul_ne_zero hcentralFine hreducedMixed
  have hpair : cmp89Eq249CentralEntireAveragePair 4 M 1 mixed ≠ 0 := by
    exact cmp89Eq249CentralEntireAveragePair_mixedCoarse_ne_zero
      hrho hpairWindow ell physicalCoordinate
  exact ⟨hfine, hstabilized,
    cmp89Eq246CentralAverageRow_ne_zero_of_pair_ne_zero 4 M 1 mixed hpair⟩

/-- Finset-indexed form of the mixed representative, used to telescope from
the all-physical endpoint to the all-centered endpoint. -/
def cmp99SourceFlatFullPointSourceMixedMomentumOn
    {N' : ℕ} [NeZero N'] (ell : FinBox 4 N')
    (s : Finset (Fin 4)) : Fin 4 → ℂ :=
  cmp99SourceFlatFullPointSourceMixedMomentum ell
    (fun mu => decide (mu ∈ s))

/-- The complete two-endpoint Eq. (2.46) integrand agrees at the centered and
literal physical coarse representatives.  Each coordinate is changed only
after constructing both adjacent mixed domains; no periodicity is asserted
outside those domains. -/
theorem cmp89Eq246PhysicalFineToFineGreenIntegrand_centered_eq_physical
    {M N' : ℕ} [NeZero M] [NeZero N'] {a rho : ℝ}
    (ha : 0 < a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (target source : Fin 4 → ℤ) (ell : FinBox 4 N') :
    cmp89Eq246PhysicalFineToFineGreenIntegrand M 1 0 a
        (fun mu =>
          (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ))
        target source =
      cmp89Eq246PhysicalFineToFineGreenIntegrand M 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        target source := by
  classical
  by_cases hell : ell = 0
  · subst ell
    have hmomentum :
        (fun mu =>
          (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum
            (0 : FinBox 4 N') mu : ℂ)) =
          cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            (0 : FinBox 4 N') := by
      funext mu
      rcases
          cmp99SourceFlatQprime_centered_eq_physical_or_add_period
            (0 : FinBox 4 N') mu with heq | hperiod
      · exact heq
      · have hphysicalZero :
            cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
                (0 : FinBox 4 N') mu = 0 := by
            simp [cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum]
        have hcenteredAbs :=
          abs_cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_le_pi
            (0 : FinBox 4 N') mu
        have hcenteredUpper := (abs_le.mp hcenteredAbs).2
        rw [hphysicalZero] at hperiod
        have hreal := congrArg Complex.re hperiod
        simp at hreal
        have : False := by nlinarith [Real.pi_pos]
        exact this.elim
    rw [hmomentum]
  · let centered : Fin 4 → ℂ := fun mu =>
      (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ)
    let physical : Fin 4 → ℂ :=
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
    let F : (Fin 4 → ℂ) → ℂ := fun z =>
      cmp89Eq246PhysicalFineToFineGreenIntegrand M 1 0 a z target source
    have hstage : ∀ s : Finset (Fin 4),
        F (cmp99SourceFlatFullPointSourceMixedMomentumOn ell s) =
          F centered := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          congr 1
          funext mu
          simp [cmp99SourceFlatFullPointSourceMixedMomentumOn,
            cmp99SourceFlatFullPointSourceMixedMomentum, centered]
      | @insert mu s hmu ih =>
          let zPhysical :=
            cmp99SourceFlatFullPointSourceMixedMomentumOn ell (insert mu s)
          let zCentered :=
            cmp99SourceFlatFullPointSourceMixedMomentumOn ell s
          have hdomainPhysical :
              CMP89Eq246FullSolutionDomain 4 M 1 0 a zPhysical := by
            exact cmp99SourceFlatFullPointSourceSolutionDomain_mixed
              ha hrho hamplitude hradius hdenWindow hpairWindow hell
              (fun k => decide (k ∈ insert mu s))
          have hdomainCentered :
              CMP89Eq246FullSolutionDomain 4 M 1 0 a zCentered := by
            exact cmp99SourceFlatFullPointSourceSolutionDomain_mixed
              ha hrho hamplitude hradius hdenWindow hpairWindow hell
              (fun k => decide (k ∈ s))
          rcases
              cmp99SourceFlatQprime_centered_eq_physical_or_add_period ell mu
            with heq | hperiod
          · have hz : zPhysical = zCentered := by
              funext k
              by_cases hk : k = mu
              · subst k
                simp [zPhysical, zCentered,
                  cmp99SourceFlatFullPointSourceMixedMomentumOn,
                  cmp99SourceFlatFullPointSourceMixedMomentum, hmu, heq]
              · simp [zPhysical, zCentered,
                  cmp99SourceFlatFullPointSourceMixedMomentumOn,
                  cmp99SourceFlatFullPointSourceMixedMomentum, hk]
            rw [hz]
            exact ih
          · have hz :
                cmp89Eq248PhysicalCoordinatePeriodShift mu zPhysical =
                  zCentered := by
              funext k
              by_cases hk : k = mu
              · subst k
                simp [zPhysical, zCentered,
                  cmp99SourceFlatFullPointSourceMixedMomentumOn,
                  cmp99SourceFlatFullPointSourceMixedMomentum,
                  cmp89Eq248PhysicalCoordinatePeriodShift, hmu, hperiod]
              · simp [zPhysical, zCentered,
                  cmp99SourceFlatFullPointSourceMixedMomentumOn,
                  cmp99SourceFlatFullPointSourceMixedMomentum,
                  cmp89Eq248PhysicalCoordinatePeriodShift, hk]
            have hperiodic :=
              cmp89Eq246PhysicalFineToFineGreenIntegrand_periodShift
                M 1 0 a mu zPhysical target source
                hdomainPhysical (by simpa only [hz] using hdomainCentered)
            rw [hz] at hperiodic
            exact hperiodic.symm.trans ih
    have hall := hstage Finset.univ
    have hphysical :
        cmp99SourceFlatFullPointSourceMixedMomentumOn ell Finset.univ =
          physical := by
      funext mu
      simp [cmp99SourceFlatFullPointSourceMixedMomentumOn,
        cmp99SourceFlatFullPointSourceMixedMomentum, physical]
    rw [hphysical] at hall
    exact hall.symm

end

end YangMills.RG
