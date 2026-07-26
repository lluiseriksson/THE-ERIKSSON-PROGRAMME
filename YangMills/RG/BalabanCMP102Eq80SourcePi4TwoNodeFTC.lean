/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondMixedPotentialRegularity

/-!
# Two-coordinate physical CMP102 FTC data

This module prepares the literal depth-two FTC tree.  It proves that the two
orders of updating fresh weakening coordinates give the same covariance and
that the first mixed covariance carried along the second coordinate is exactly
the directional propagator appearing at the root node.
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

/-- Two fresh real weakening updates commute inside every fixed mixed
covariance carrier. -/
theorem cmp116SourcePi4RealMixedCovarianceOperatorCurve_update_comm
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d e : FinBox 4 (2 * Q)) (hde : d ≠ e)
    (t u : ℝ) :
    cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK (Function.update s d t) S e u =
      cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK (Function.update s e u) S d t := by
  rw [cmp116SourcePi4RealMixedCovarianceOperatorCurve_eq,
    cmp116SourcePi4RealMixedCovarianceOperatorCurve_eq,
    Function.update_comm hde t u s]

/-- Along a fresh second coordinate, the first mixed covariance is literally
the root directional propagator. -/
theorem cmp116SourcePi4FirstMixedCovarianceCurve_eq_rootDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d e : FinBox 4 (2 * Q)) (hde : d ≠ e)
    (t u : ℝ) :
    cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK
        (Function.update s d t) (insert d S) e u =
      cmp116SourcePi4RealMixedCovarianceOperatorDerivative
        (R := R) anchor K hc hmass hK
        (Function.update s e u) S d := by
  rw [cmp116SourcePi4RealMixedCovarianceOperatorCurve_eq,
    cmp116SourcePi4RealMixedCovarianceOperatorDerivative_eq,
    Function.update_comm hde t u s,
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_update_of_mem
      anchor K hc hmass hK (Function.update s e u) (insert d S) d
      (Finset.mem_insert_self d S) t]

/-- The literal first directional derivative, transported along a second
fresh weakening coordinate. -/
noncomputable def cmp102Eq80SourcePi4SecondMixedDirectionalCurve
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
  cmp102Eq80PropagatorDirectionalDerivative D D₃
    (cmp116SourcePi4RealMixedCovarianceOperatorCurve
      (R := R) anchor K hc hmass hK
      (Function.update s d t) ∅ e u)
    (cmp116SourcePi4RealMixedCovarianceOperatorCurve
      (R := R) anchor K hc hmass hK
      (Function.update s d t) {d} e u)
    Δπ J A
    (fderiv ℝ V₀
      (A -
        cmp116SourcePi4RealMixedCovarianceOperatorCurve
          (R := R) anchor K hc hmass hK
          (Function.update s d t) ∅ e u (D A)))

/-- The transported second-coordinate curve is exactly the named first
directional derivative at the root with the second coordinate fixed to `u`. -/
theorem cmp102Eq80SourcePi4SecondMixedDirectionalCurve_eq_rootDerivative
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
    (t u : ℝ)
    (A : PhysicalField M Q Nc) :
    cmp102Eq80SourcePi4SecondMixedDirectionalCurve
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s d e t u A =
      cmp102Eq80SourcePi4RealMixedPotentialCurveDerivative
        (R := R) anchor K hc hmass hK D D₃ Δπ J
        (Function.update s e u) ∅ d A t
        (fderiv ℝ V₀
          (A -
            cmp116SourcePi4RealMixedCovarianceOperatorCurve
              (R := R) anchor K hc hmass hK
              (Function.update s e u) ∅ d t (D A))) := by
  unfold cmp102Eq80SourcePi4SecondMixedDirectionalCurve
    cmp102Eq80SourcePi4RealMixedPotentialCurveDerivative
  rw [cmp116SourcePi4RealMixedCovarianceOperatorCurve_update_comm
      anchor K hc hmass hK s ∅ d e hde t u]
  rw [show
    cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK
        (Function.update s d t) {d} e u =
      cmp116SourcePi4RealMixedCovarianceOperatorDerivative
        (R := R) anchor K hc hmass hK
        (Function.update s e u) ∅ d by
    simpa using
      cmp116SourcePi4FirstMixedCovarianceCurve_eq_rootDerivative
        anchor K hc hmass hK s ∅ d e hde t u]

/-- The second physical directional curve is `C¹` on the certified real
contour. -/
theorem contDiff_one_cmp102Eq80SourcePi4SecondMixedDirectionalCurve'
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
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ 2 V₀) :
    ContDiff ℝ 1
      (cmp102Eq80SourcePi4SecondMixedDirectionalCurve
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s d e t · A) := by
  exact
    contDiff_one_cmp102Eq80SourcePi4SecondMixedDirectionalCurve
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 D D₃ V₀ Δπ J s d e hed t ht hRweak hs hcap hsmall A hV₀

end

end YangMills.RG
