/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SingletonFTCValidity

/-!
# Regularity of the second physical CMP102 weakening node

After the first weakening derivative, the complete directional functional
depends simultaneously on the covariance `H`, its first mixed derivative
`H_d`, and `fderiv V₀`.  This module proves `C¹` regularity of that literal
functional when a fresh second coordinate varies.
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

private theorem update_real_unitShifted
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (d : D) (t : ℝ)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖((Function.update s d t x : ℝ) : ℂ) - 1‖ ≤ (1 : ℝ) := by
  intro x
  by_cases hxd : x = d
  · subst x
    simp only [Function.update_self]
    have ht01 : 0 ≤ t ∧ t ≤ 1 := by
      simpa [Set.mem_uIcc] using ht
    rw [show (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr ht01.2)]
    linarith
  · simpa [Function.update_of_ne hxd] using hs x

private theorem update_real_cap
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (d : D) (t Rweak : ℝ)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak) :
    ∀ x, ‖((Function.update s d t x : ℝ) : ℂ)‖ ≤ Rweak := by
  intro x
  by_cases hxd : x = d
  · subst x
    simp only [Function.update_self, Complex.norm_real]
    have ht01 : 0 ≤ t ∧ t ≤ 1 := by
      simpa [Set.mem_uIcc] using ht
    rw [Real.norm_eq_abs, abs_of_nonneg ht01.1]
    exact ht01.2.trans hRweak
  · simpa [Function.update_of_ne hxd] using hcap x

set_option maxHeartbeats 3500000 in
/-- The literal first directional derivative is `C¹` when a fresh second
source weakening coordinate varies.  Both the covariance and its first mixed
derivative are generated from the physical contour series. -/
theorem
    contDiff_one_cmp102Eq80SourcePi4SecondMixedDirectionalCurve
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
    ContDiff ℝ 1 fun u =>
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
              (Function.update s d t) ∅ e u (D A))) := by
  have hsdt :
      ∀ x, ‖((Function.update s d t x : ℝ) : ℂ) - 1‖ ≤ (1 : ℝ) :=
    update_real_unitShifted s d t ht hs
  have hcapdt :
      ∀ x, ‖((Function.update s d t x : ℝ) : ℂ)‖ ≤ Rweak :=
    update_real_cap s d t Rweak ht hRweak hcap
  have hH :
      ContDiff ℝ 1
        (cmp116SourcePi4RealMixedCovarianceOperatorCurve
          (R := R) anchor K hc hmass hK
          (Function.update s d t) ∅ e) :=
    contDiff_one_cmp116SourcePi4RealMixedCovarianceOperatorCurve_ofPhysicalContour
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 (Function.update s d t) ∅ e (by simp)
      hRweak hsdt hcapdt hsmall
  have hHd :
      ContDiff ℝ 1
        (cmp116SourcePi4RealMixedCovarianceOperatorCurve
          (R := R) anchor K hc hmass hK
          (Function.update s d t) {d} e) :=
    contDiff_one_cmp116SourcePi4RealMixedCovarianceOperatorCurve_ofPhysicalContour
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 (Function.update s d t) {d} e (by simpa [Finset.mem_singleton])
      hRweak hsdt hcapdt hsmall
  exact
    contDiff_cmp102Eq80PropagatorDirectionalDerivative_families
      D D₃ V₀
      (cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK
        (Function.update s d t) ∅ e)
      (cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK
        (Function.update s d t) {d} e)
      Δπ J A hH hHd hV₀

end

end YangMills.RG
