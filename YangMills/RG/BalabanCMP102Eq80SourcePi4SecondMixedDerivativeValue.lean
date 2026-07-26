/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SecondPropagatorDerivative
import YangMills.RG.BalabanCMP102Eq80SourcePi4TwoNodeFTC

/-!
# The literal physical derivative at the second CMP102 FTC node

The second-node curve was already constructed from the complete physical
mixed covariance.  Here its derivative is identified exactly with the
second propagator formula: the next mixed covariance, the quadratic cross
term, and the actual Fréchet Hessian of `V₀`.

Both operator derivative recurrences are produced from the physical contour
certificate.  No derivative or domain coefficient is supplied by the caller.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Literal value of the derivative at the second physical FTC node. -/
noncomputable def cmp102Eq80SourcePi4SecondMixedDerivativeValue
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
    (t u : ℝ)
    (A : PhysicalField M Q Nc) : ℝ :=
  let sdt := Function.update s d t
  let H :=
    cmp116SourcePi4RealMixedCovarianceOperatorCurve
      (R := R) anchor K hc hmass hK sdt ∅ e u
  let Hd :=
    cmp116SourcePi4RealMixedCovarianceOperatorCurve
      (R := R) anchor K hc hmass hK sdt {d} e u
  let He :=
    cmp116SourcePi4RealMixedCovarianceOperatorDerivative
      (R := R) anchor K hc hmass hK sdt ∅ e
  let Hde :=
    cmp116SourcePi4RealMixedCovarianceOperatorDerivative
      (R := R) anchor K hc hmass hK sdt {d} e
  let shifted := A - H (D A)
  cmp102Eq80SecondPropagatorMixedDerivative D D₃
    H Hd He Hde Δπ J A
    (fderiv ℝ V₀ shifted)
    (fderiv ℝ (fderiv ℝ V₀) shifted)

set_option maxHeartbeats 3000000 in
/-- The actual second-node physical curve has the literal second mixed
equation-(80) derivative above. -/
theorem hasDerivAt_cmp102Eq80SourcePi4SecondMixedDirectionalCurve
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
    (d e : FinBox 4 (2 * Q)) (hed : e ≠ d)
    (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1)
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (u : ℝ)
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ 2 V₀) :
    HasDerivAt
      (cmp102Eq80SourcePi4SecondMixedDirectionalCurve
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        s d e t · A)
      (cmp102Eq80SourcePi4SecondMixedDerivativeValue
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        s d e t u A) u := by
  let sdt := Function.update s d t
  have hsdt :
      ∀ x, ‖((sdt x : ℝ) : ℂ) - 1‖ ≤ (1 : ℝ) := by
    exact cmp116UpdateRealWeakening_unitShifted s d t ht hs
  have hcapdt :
      ∀ x, ‖((sdt x : ℝ) : ℂ)‖ ≤ Rweak := by
    exact cmp116UpdateRealWeakening_cap s d t Rweak ht hRweak hcap
  have hH :
      HasDerivAt
        (cmp116SourcePi4RealMixedCovarianceOperatorCurve
          (R := R) anchor K hc hmass hK sdt ∅ e)
        (cmp116SourcePi4RealMixedCovarianceOperatorDerivative
          (R := R) anchor K hc hmass hK sdt ∅ e) u :=
    (CMP116SourcePi4RealMixedDerivativeCertificate.ofPhysicalContour
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 sdt ∅ e (by simp) hRweak hsdt hcapdt hsmall u
      ).hasDerivAt_operator
  have heSingleton : e ∉ ({d} : Finset (FinBox 4 (2 * Q))) := by
    simpa [Finset.mem_singleton] using hed
  have hHd :
      HasDerivAt
        (cmp116SourcePi4RealMixedCovarianceOperatorCurve
          (R := R) anchor K hc hmass hK sdt {d} e)
        (cmp116SourcePi4RealMixedCovarianceOperatorDerivative
          (R := R) anchor K hc hmass hK sdt {d} e) u :=
    (CMP116SourcePi4RealMixedDerivativeCertificate.ofPhysicalContour
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 sdt {d} e heSingleton hRweak hsdt hcapdt hsmall u
      ).hasDerivAt_operator
  simpa [cmp102Eq80SourcePi4SecondMixedDirectionalCurve,
    cmp102Eq80SourcePi4SecondMixedDerivativeValue, sdt] using
    hasDerivAt_cmp102Eq80PropagatorDirectionalDerivative_fderivCurve
      D D₃ V₀
      (cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK sdt ∅ e)
      (cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK sdt {d} e)
      (cmp116SourcePi4RealMixedCovarianceOperatorDerivative
        (R := R) anchor K hc hmass hK sdt ∅ e)
      (cmp116SourcePi4RealMixedCovarianceOperatorDerivative
        (R := R) anchor K hc hmass hK sdt {d} e)
      Δπ J A u hH hHd hV₀

end

end YangMills.RG
