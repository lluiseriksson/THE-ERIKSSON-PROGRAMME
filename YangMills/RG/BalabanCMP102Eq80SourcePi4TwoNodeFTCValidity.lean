/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4TwoNodeFTC

/-!
# Validity of the physical two-coordinate CMP102 FTC tree

Every analytic obligation of the literal depth-two tree is discharged from
the physical contour certificate and `C²` regularity of `V₀`.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

set_option maxHeartbeats 6000000 in
/-- The source-specific depth-two FTC tree is valid on the certified real
weakening contour. -/
theorem cmp102Eq80SourcePi4TwoNodeFTCExpansionTree_valid
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
    (cmp102Eq80SourcePi4TwoNodeFTCExpansionTree
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      s d e A).Valid := by
  let se : FinBox 4 (2 * Q) → ℝ := Function.update s e 1
  let sd : FinBox 4 (2 * Q) → ℝ := Function.update s d 0
  have hseShift : ∀ x, ‖(se x : ℂ) - 1‖ ≤ (1 : ℝ) :=
    cmp116UpdateRealWeakening_unitShifted s e 1 (by simp) hs
  have hseCap : ∀ x, ‖(se x : ℂ)‖ ≤ Rweak :=
    cmp116UpdateRealWeakening_cap s e 1 Rweak (by simp) hRweak hcap
  have hsdShift : ∀ x, ‖(sd x : ℂ) - 1‖ ≤ (1 : ℝ) :=
    cmp116UpdateRealWeakening_unitShifted s d 0 (by simp) hs
  have hsdCap : ∀ x, ‖(sd x : ℂ)‖ ≤ Rweak :=
    cmp116UpdateRealWeakening_cap s d 0 Rweak (by simp) hRweak hcap
  have hV₀one : ContDiff ℝ 1 V₀ := hV₀.of_le (by norm_num)
  have hbaseValid :
      (cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sd [e] A).Valid :=
    cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree_valid_singleton
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 D D₃ V₀ Δπ J sd e hRweak hsdShift hsdCap hsmall A hV₀one
  have hbaseSum :
      (cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sd [e] A).expansionSum =
        cmp102Eq80SourcePi4RealMixedPotential
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          (Function.update se d 0) ∅ A := by
    calc
      _ = (cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            sd [e] A).coupledEndpoint :=
        CMP116FTCExpansionTree.expansionSum_eq_coupledEndpoint _ hbaseValid
      _ = cmp102Eq80SourcePi4RealMixedPotential
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            (cmp116SetRealWeakeningList sd [e] 1) ∅ A :=
        cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree_coupledEndpoint
          anchor K hc hmass hK D D₃ V₀ Δπ J sd [e] (by simp) A
      _ = _ := by
        rw [cmp116SetRealWeakeningList_cons_of_not_mem sd e [] 1 (by simp),
          cmp116SetRealWeakeningList_nil]
        exact congrArg
          (fun sigma =>
            cmp102Eq80SourcePi4RealMixedPotential
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma ∅ A)
          (Function.update_comm hde 0 1 s)
  have hfiber :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        (cmp116FTCExpansionTreeOfCurve
          (cmp102Eq80SourcePi4SecondMixedDirectionalCurve
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            s d e t · A)).Valid ∧
        (cmp116FTCExpansionTreeOfCurve
          (cmp102Eq80SourcePi4SecondMixedDirectionalCurve
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            s d e t · A)).expansionSum =
          cmp102Eq80SourcePi4SecondMixedDirectionalCurve
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            s d e t 1 A := by
    intro t ht
    have hcurve :=
      contDiff_one_cmp102Eq80SourcePi4SecondMixedDirectionalCurve'
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
        hΔ hΔ1 D D₃ V₀ Δπ J s d e hde.symm t ht
        hRweak hs hcap hsmall A hV₀
    have hvalid :=
      cmp116FTCExpansionTreeOfCurve_valid
        (cmp102Eq80SourcePi4SecondMixedDirectionalCurve
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          s d e t · A) hcurve
    refine ⟨hvalid, ?_⟩
    simpa [cmp116FTCExpansionTreeOfCurve,
      CMP116FTCExpansionTree.coupledEndpoint] using
      CMP116FTCExpansionTree.expansionSum_eq_coupledEndpoint _ hvalid
  have hrootDeriv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt
          (fun u =>
            cmp102Eq80SourcePi4RealMixedPotential
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
              (Function.update se d u) ∅ A)
          (cmp102Eq80SourcePi4SecondMixedDirectionalCurve
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            s d e t 1 A) t := by
    intro t _ht
    have hfirst :=
      hasDerivAt_cmp102Eq80SourcePi4RealWeakeningCoordinateDerivative
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
        hΔ hΔ1 D D₃ V₀ Δπ J se d hRweak hseShift hseCap hsmall
        A hV₀one t
    let Cert :=
      CMP116SourcePi4RealMixedDerivativeCertificate.ofPhysicalContour
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
        hΔ hΔ1 se ∅ d (by simp) hRweak hseShift hseCap hsmall t
    have hV₀At :
        HasFDerivAt V₀ (fderiv ℝ V₀
          (A -
            cmp116SourcePi4RealMixedCovarianceOperatorCurve
              (R := R) anchor K hc hmass hK se ∅ d t (D A)))
          (A -
            cmp116SourcePi4RealMixedCovarianceOperatorCurve
              (R := R) anchor K hc hmass hK se ∅ d t (D A)) :=
      (hV₀one.differentiable one_ne_zero _).hasFDerivAt
    have hvalue :=
      Cert.realWeakeningDerivative_eq
        anchor K hc hmass hK D D₃ V₀ Δπ J se d A t
        (fderiv ℝ V₀
          (A -
            cmp116SourcePi4RealMixedCovarianceOperatorCurve
              (R := R) anchor K hc hmass hK se ∅ d t (D A)))
        hV₀At
    have hsecond :=
      cmp102Eq80SourcePi4SecondMixedDirectionalCurve_eq_rootDerivative
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s d e hde t 1 A
    exact hfirst.congr_deriv (hvalue.trans hsecond.symm)
  have hrootContinuous :
      Continuous fun t =>
        cmp102Eq80SourcePi4SecondMixedDirectionalCurve
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          s d e t 1 A := by
    have hphysical :=
      continuous_cmp102Eq80SourcePi4RealMixedPotentialCurveDerivative
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
        hΔ hΔ1 D D₃ V₀ Δπ J se ∅ d (by simp)
        hRweak hseShift hseCap hsmall A hV₀one
    apply hphysical.congr
    intro t
    exact
      (cmp102Eq80SourcePi4SecondMixedDirectionalCurve_eq_rootDerivative
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s d e hde t 1 A).symm
  unfold cmp102Eq80SourcePi4TwoNodeFTCExpansionTree
  exact ⟨hbaseValid, hbaseSum, hfiber, hrootDeriv,
    hrootContinuous.intervalIntegrable 0 1⟩

end

end YangMills.RG
