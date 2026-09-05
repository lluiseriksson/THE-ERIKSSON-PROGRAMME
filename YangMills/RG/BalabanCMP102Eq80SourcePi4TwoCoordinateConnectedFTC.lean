/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4TwoNodeFTCValidity

/-!
# The physical two-coordinate connected FTC coefficient

The second source coordinate is no longer frozen at its coupled endpoint.
For every `u ∈ [0,1]`, the literal first directional functional is proved to
be the derivative of the equation-(80) potential along the first coordinate.
This is the calculus input needed to identify the four-endpoint connected
increment with a genuine iterated integral.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

set_option maxHeartbeats 4000000 in
/-- At every physical interpolation value of the second coordinate, the
transported first directional functional is the actual derivative in the
first coordinate. -/
theorem hasDerivAt_cmp102Eq80SourcePi4RootCurve_secondMixedDirectional
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (d e : FinBox 4 (2 * Q)) (hde : d ≠ e)
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀)
    (t u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) 1) :
    HasDerivAt
      (fun v =>
        cmp102Eq80SourcePi4RealMixedPotential
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          (Function.update (Function.update s e u) d v) ∅ A)
      (cmp102Eq80SourcePi4SecondMixedDirectionalCurve
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        s d e t u A) t := by
  let su : FinBox 4 (2 * Q) → ℝ := Function.update s e u
  have hsuShift : ∀ x, ‖(su x : ℂ) - 1‖ ≤ (1 : ℝ) :=
    cmp116UpdateRealWeakening_unitShifted s e u hu hs
  have hsuCap : ∀ x, ‖(su x : ℂ)‖ ≤ Rweak :=
    cmp116UpdateRealWeakening_cap s e u Rweak hu hRweak hcap
  have hfirst :=
    hasDerivAt_cmp102Eq80SourcePi4RealWeakeningCoordinateDerivative
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 D D₃ V₀ Δπ J su d hRweak hsuShift hsuCap hsmall A hV₀ t
  let Cert :=
    CMP116SourcePi4RealMixedDerivativeCertificate.ofPhysicalContour
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 su ∅ d (by simp) hRweak hsuShift hsuCap hsmall t
  have hV₀At :
      HasFDerivAt V₀ (fderiv ℝ V₀
        (A -
          cmp116SourcePi4RealMixedCovarianceOperatorCurve
            (R := R) anchor K hc hmass hK su ∅ d t (D A)))
        (A -
          cmp116SourcePi4RealMixedCovarianceOperatorCurve
            (R := R) anchor K hc hmass hK su ∅ d t (D A)) :=
    (hV₀.differentiable one_ne_zero _).hasFDerivAt
  have hvalue :=
    Cert.realWeakeningDerivative_eq
      anchor K hc hmass hK D D₃ V₀ Δπ J su d A t
      (fderiv ℝ V₀
        (A -
          cmp116SourcePi4RealMixedCovarianceOperatorCurve
            (R := R) anchor K hc hmass hK su ∅ d t (D A)))
      hV₀At
  have hsecond :=
    cmp102Eq80SourcePi4SecondMixedDirectionalCurve_eq_rootDerivative
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      s d e hde t u A
  exact hfirst.congr_deriv (hvalue.trans hsecond.symm)

set_option maxHeartbeats 3000000 in
/-- For fixed physical value of the second coordinate, the transported first
directional functional is continuous in the first interpolation value. -/
theorem continuous_cmp102Eq80SourcePi4SecondMixedDirectionalCurve_left
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (d e : FinBox 4 (2 * Q)) (hde : d ≠ e)
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀)
    (u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) 1) :
    Continuous fun t =>
      cmp102Eq80SourcePi4SecondMixedDirectionalCurve
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        s d e t u A := by
  let su : FinBox 4 (2 * Q) → ℝ := Function.update s e u
  have hsuShift : ∀ x, ‖(su x : ℂ) - 1‖ ≤ (1 : ℝ) :=
    cmp116UpdateRealWeakening_unitShifted s e u hu hs
  have hsuCap : ∀ x, ‖(su x : ℂ)‖ ≤ Rweak :=
    cmp116UpdateRealWeakening_cap s e u Rweak hu hRweak hcap
  have hphysical :=
    continuous_cmp102Eq80SourcePi4RealMixedPotentialCurveDerivative
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 D D₃ V₀ Δπ J su ∅ d (by simp)
      hRweak hsuShift hsuCap hsmall A hV₀
  apply hphysical.congr
  intro t
  exact
    (cmp102Eq80SourcePi4SecondMixedDirectionalCurve_eq_rootDerivative
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      s d e hde t u A).symm

/-- The alternating four-endpoint coefficient of the literal physical
equation-(80) weakening functional. -/
noncomputable def cmp102Eq80SourcePi4TwoCoordinateConnectedIncrement
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (d e : FinBox 4 (2 * Q))
    (A : PhysicalField M Q Nc) : ℝ :=
  let F := fun t u =>
    cmp102Eq80SourcePi4RealMixedPotential
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      (Function.update (Function.update s e u) d t) ∅ A
  F 1 1 - F 1 0 - F 0 1 + F 0 0

/-- The connected coefficient depends on the unordered pair of distinct
weakening coordinates, not on the order used to perform FTC. -/
theorem cmp102Eq80SourcePi4TwoCoordinateConnectedIncrement_comm
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (d e : FinBox 4 (2 * Q)) (hde : d ≠ e)
    (A : PhysicalField M Q Nc) :
    cmp102Eq80SourcePi4TwoCoordinateConnectedIncrement
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s d e A =
      cmp102Eq80SourcePi4TwoCoordinateConnectedIncrement
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s e d A := by
  simp only [cmp102Eq80SourcePi4TwoCoordinateConnectedIncrement]
  rw [Function.update_comm hde 1 1 s,
    Function.update_comm hde 1 0 s,
    Function.update_comm hde 0 1 s,
    Function.update_comm hde 0 0 s]
  ring

set_option maxHeartbeats 7000000 in
/-- The physical connected two-coordinate coefficient is exactly the nested
integral of the genuine second mixed weakening derivative. -/
theorem cmp102Eq80SourcePi4TwoCoordinateConnectedIncrement_eq_iteratedFTC
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (d e : FinBox 4 (2 * Q)) (hde : d ≠ e)
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ 2 V₀) :
    cmp102Eq80SourcePi4TwoCoordinateConnectedIncrement
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s d e A =
      ∫ t in (0 : ℝ)..1,
        ∫ u in (0 : ℝ)..1,
          deriv (fun v =>
            cmp102Eq80SourcePi4SecondMixedDirectionalCurve
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
              s d e t v A) u := by
  have hV₀one : ContDiff ℝ 1 V₀ := hV₀.of_le (by norm_num)
  have hinner :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        (∫ u in (0 : ℝ)..1,
          deriv (fun v =>
            cmp102Eq80SourcePi4SecondMixedDirectionalCurve
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
              s d e t v A) u) =
          cmp102Eq80SourcePi4SecondMixedDirectionalCurve
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
              s d e t 1 A -
            cmp102Eq80SourcePi4SecondMixedDirectionalCurve
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
              s d e t 0 A := by
    intro t ht
    have hcurve :=
      contDiff_one_cmp102Eq80SourcePi4SecondMixedDirectionalCurve'
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
        hΔ hΔ1 D D₃ V₀ Δπ J s d e hde.symm t ht
        hRweak hs hcap hsmall A hV₀
    rw [contDiff_one_iff_deriv] at hcurve
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _hu => (hcurve.1 u).hasDerivAt)
      (hcurve.2.intervalIntegrable 0 1)
  have houter :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        (∫ t in (0 : ℝ)..1,
          cmp102Eq80SourcePi4SecondMixedDirectionalCurve
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            s d e t u A) =
          cmp102Eq80SourcePi4RealMixedPotential
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
              (Function.update (Function.update s e u) d 1) ∅ A -
            cmp102Eq80SourcePi4RealMixedPotential
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
              (Function.update (Function.update s e u) d 0) ∅ A := by
    intro u hu
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ht =>
        hasDerivAt_cmp102Eq80SourcePi4RootCurve_secondMixedDirectional
          anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
          hΔ hΔ1 D D₃ V₀ Δπ J s d e hde hRweak hs hcap hsmall
          A hV₀one t u hu)
      ((continuous_cmp102Eq80SourcePi4SecondMixedDirectionalCurve_left
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
        hΔ hΔ1 D D₃ V₀ Δπ J s d e hde hRweak hs hcap hsmall
        A hV₀one u hu).intervalIntegrable 0 1)
  have hcont1 :=
    continuous_cmp102Eq80SourcePi4SecondMixedDirectionalCurve_left
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 D D₃ V₀ Δπ J s d e hde hRweak hs hcap hsmall
      A hV₀one 1 (by simp)
  have hcont0 :=
    continuous_cmp102Eq80SourcePi4SecondMixedDirectionalCurve_left
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 D D₃ V₀ Δπ J s d e hde hRweak hs hcap hsmall
      A hV₀one 0 (by simp)
  rw [show
    (∫ t in (0 : ℝ)..1,
      ∫ u in (0 : ℝ)..1,
        deriv (fun v =>
          cmp102Eq80SourcePi4SecondMixedDirectionalCurve
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            s d e t v A) u) =
      ∫ t in (0 : ℝ)..1,
        (cmp102Eq80SourcePi4SecondMixedDirectionalCurve
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            s d e t 1 A -
          cmp102Eq80SourcePi4SecondMixedDirectionalCurve
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            s d e t 0 A) by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hinner t ht]
  rw [intervalIntegral.integral_sub
    (hcont1.intervalIntegrable 0 1)
    (hcont0.intervalIntegrable 0 1), houter 1 (by simp), houter 0 (by simp)]
  unfold cmp102Eq80SourcePi4TwoCoordinateConnectedIncrement
  ring

end

end YangMills.RG
