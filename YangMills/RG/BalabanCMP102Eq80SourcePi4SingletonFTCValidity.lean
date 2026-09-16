/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4MixedPotentialFTCExpansionTree

/-!
# The first physical CMP102 weakening FTC node

This module validates the depth-one source `Pi^4` FTC tree directly on the
certified real contour.  It deliberately avoids a global smoothness claim for
the weakened covariance: the physical series is only known to converge on its
specified contour.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

set_option maxHeartbeats 2500000 in
/-- The physical contour producer differentiates the literal weakening
functional by its actual coordinate derivative. -/
theorem hasDerivAt_cmp102Eq80SourcePi4RealWeakeningCoordinateDerivative
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
    (d : FinBox 4 (2 * Q))
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀)
    (t : ℝ) :
    HasDerivAt
      (fun u =>
        cmp102Eq80SourcePi4RealMixedPotential
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          (Function.update s d u) ∅ A)
      (cmp116RealWeakeningCoordinateDerivative
        (fun sigma =>
          cmp102Eq80SourcePi4RealMixedPotential
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma ∅ A)
        d t s)
      t := by
  let Cert :=
    CMP116SourcePi4RealMixedDerivativeCertificate.ofPhysicalContour
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 s ∅ d (by simp) hRweak hs hcap hsmall t
  have hV₀At :
      HasFDerivAt V₀ (fderiv ℝ V₀
        (A -
          cmp116SourcePi4RealMixedCovarianceOperatorCurve
            (R := R) anchor K hc hmass hK s ∅ d t (D A)))
        (A -
          cmp116SourcePi4RealMixedCovarianceOperatorCurve
            (R := R) anchor K hc hmass hK s ∅ d t (D A)) :=
    (hV₀.differentiable one_ne_zero _).hasFDerivAt
  have hphysical :=
    Cert.hasDerivAt_eq80Potential
      anchor K hc hmass hK D D₃ V₀ Δπ J s ∅ d A t
      (fderiv ℝ V₀
        (A -
          cmp116SourcePi4RealMixedCovarianceOperatorCurve
            (R := R) anchor K hc hmass hK s ∅ d t (D A)))
      hV₀At
  have hvalue :=
    Cert.realWeakeningDerivative_eq
      anchor K hc hmass hK D D₃ V₀ Δπ J s d A t
      (fderiv ℝ V₀
        (A -
          cmp116SourcePi4RealMixedCovarianceOperatorCurve
            (R := R) anchor K hc hmass hK s ∅ d t (D A)))
      hV₀At
  unfold CMP116SourcePi4RealMixedEq80DerivativeStatement at hphysical
  exact (hphysical.congr_deriv hvalue.symm).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u =>
      (cmp102Eq80SourcePi4RealMixedPotentialCurve_eq
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s ∅ d A u).symm)

set_option maxHeartbeats 2500000 in
/-- The literal coordinate derivative is continuous along the certified real
interpolation line. -/
theorem continuous_cmp102Eq80SourcePi4RealWeakeningCoordinateDerivative
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
    (d : FinBox 4 (2 * Q))
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀) :
    Continuous fun t =>
      cmp116RealWeakeningCoordinateDerivative
        (fun sigma =>
          cmp102Eq80SourcePi4RealMixedPotential
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma ∅ A)
        d t s := by
  have hphysical :=
    continuous_cmp102Eq80SourcePi4RealMixedPotentialCurveDerivative
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 D D₃ V₀ Δπ J s ∅ d (by simp) hRweak hs hcap hsmall A hV₀
  apply hphysical.congr
  intro t
  let Cert :=
    CMP116SourcePi4RealMixedDerivativeCertificate.ofPhysicalContour
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 s ∅ d (by simp) hRweak hs hcap hsmall t
  exact (Cert.realWeakeningDerivative_eq
    anchor K hc hmass hK D D₃ V₀ Δπ J s d A t
    (fderiv ℝ V₀
      (A -
        cmp116SourcePi4RealMixedCovarianceOperatorCurve
          (R := R) anchor K hc hmass hK s ∅ d t (D A)))
    (hV₀.differentiable one_ne_zero _).hasFDerivAt).symm

/- A depth-one literal tree is valid as soon as its actual coordinate
derivative is certified and continuous on the interpolation interval. -/
theorem cmp116RealWeakeningFTCExpansionTree_valid_singleton_of
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) (s : D → ℝ) (d : D)
    (hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt
        (fun u => f (Function.update s d u))
        (cmp116RealWeakeningCoordinateDerivative f d t s) t)
    (hcontinuous :
      Continuous fun t =>
        cmp116RealWeakeningCoordinateDerivative f d t s) :
    (cmp116RealWeakeningFTCExpansionTree f s [d]).Valid := by
  simp only [cmp116RealWeakeningFTCExpansionTree,
    cmp116SetRealWeakeningList_nil]
  exact ⟨trivial, rfl, (fun t _ => ⟨trivial,
    cmp116RealWeakeningCoordinateDerivative_update_same f d t t s⟩), hderiv,
    hcontinuous.intervalIntegrable 0 1⟩

set_option maxHeartbeats 2500000 in
/-- The first source-specific FTC node is valid on the physical real contour.
No global smoothness outside that contour is assumed. -/
theorem cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree_valid_singleton
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
    (d : FinBox 4 (2 * Q))
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀) :
    (cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s [d] A).Valid := by
  apply cmp116RealWeakeningFTCExpansionTree_valid_singleton_of
  · intro t _ht
    exact
      hasDerivAt_cmp102Eq80SourcePi4RealWeakeningCoordinateDerivative
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
        hΔ hΔ1 D D₃ V₀ Δπ J s d hRweak hs hcap hsmall A hV₀ t
  · exact
      continuous_cmp102Eq80SourcePi4RealWeakeningCoordinateDerivative
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
        hΔ hΔ1 D D₃ V₀ Δπ J s d hRweak hs hcap hsmall A hV₀

end

end YangMills.RG
