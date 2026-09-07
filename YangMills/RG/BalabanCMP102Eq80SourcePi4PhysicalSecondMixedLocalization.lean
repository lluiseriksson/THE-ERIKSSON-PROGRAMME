/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondMixedLocalization

/-!
# End-to-end localization of the physical second CMP102 FTC node

This module specializes the complete second mixed source decomposition to
the actual two-coordinate physical curve.  The two interpolation parameters
are first inserted into one common weakening field.  Mixed derivatives are
independent of coordinates already present in their carrier, so `H_e` and
`H_de` are transported to that same field without changing their value.

The result identifies the derivative produced by the physical contour
certificate with a finite sum of connected, full-`Pi^4` source-domain
coefficients.  This is the first nontrivial recursive fiber of the literal
equation-(80) FTC tree.
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

/-- One source-domain coefficient of the actual physical second FTC node. -/
noncomputable def cmp102Eq80SourcePi4PhysicalSecondMixedDomainCoefficient
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
    (A : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q))) : ℝ :=
  let sue := Function.update (Function.update s d t) e u
  let H :=
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
      (R := R) anchor K hc hmass hK sue ∅
  let shifted := A - H (D A)
  cmp102Eq80SourcePi4SecondMixedDomainCoefficient
    (R := R) anchor K hc hmass hK sue (insert e {d}) {e} {d}
    D D₃ H Δπ J A
    (fderiv ℝ V₀ shifted)
    (fderiv ℝ (fderiv ℝ V₀) shifted) W

/-- The physical second-node coefficient vanishes off full-carrier labels.
-/
theorem
    cmp102Eq80SourcePi4PhysicalSecondMixedDomainCoefficient_eq_zero_of_not_subset
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
    (d e : FinBox 4 (2 * Q)) (t u : ℝ)
    (A : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q)))
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ W) :
    cmp102Eq80SourcePi4PhysicalSecondMixedDomainCoefficient
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      s d e t u A W = 0 := by
  unfold cmp102Eq80SourcePi4PhysicalSecondMixedDomainCoefficient
  exact
    cmp102Eq80SourcePi4SecondMixedDomainCoefficient_eq_zero_of_not_subset
      anchor K hc hmass hK
      (Function.update (Function.update s d t) e u)
      (insert e {d}) {e} {d} D D₃
      (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK
        (Function.update (Function.update s d t) e u) ∅)
      Δπ J A
      (fderiv ℝ V₀
        (A -
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK
            (Function.update (Function.update s d t) e u) ∅ (D A)))
      (fderiv ℝ (fderiv ℝ V₀)
        (A -
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK
            (Function.update (Function.update s d t) e u) ∅ (D A)))
      W hanchor

/-- The physical second-node coefficient vanishes on disconnected labels.
-/
theorem
    cmp102Eq80SourcePi4PhysicalSecondMixedDomainCoefficient_eq_zero_of_not_walkConnected
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
    (d e : FinBox 4 (2 * Q)) (t u : ℝ)
    (A : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) W) :
    cmp102Eq80SourcePi4PhysicalSecondMixedDomainCoefficient
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      s d e t u A W = 0 := by
  unfold cmp102Eq80SourcePi4PhysicalSecondMixedDomainCoefficient
  exact
    cmp102Eq80SourcePi4SecondMixedDomainCoefficient_eq_zero_of_not_walkConnected
      anchor K hc hmass hK
      (Function.update (Function.update s d t) e u)
      (insert e {d}) {e} {d} D D₃
      (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK
        (Function.update (Function.update s d t) e u) ∅)
      Δπ J A
      (fderiv ℝ V₀
        (A -
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK
            (Function.update (Function.update s d t) e u) ∅ (D A)))
      (fderiv ℝ (fderiv ℝ V₀)
        (A -
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK
            (Function.update (Function.update s d t) e u) ∅ (D A)))
      W hconnected

set_option maxHeartbeats 3500000 in
/-- End-to-end finite source decomposition of the derivative at the actual
physical second FTC node. -/
theorem
    cmp102Eq80SourcePi4SecondMixedDerivativeValue_eq_sum_physicalDomains
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
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
    (d e : FinBox 4 (2 * Q))
    (t u : ℝ)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1)
    (hu : u ∈ Set.uIcc (0 : ℝ) 1)
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc) :
    cmp102Eq80SourcePi4SecondMixedDerivativeValue
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        s d e t u A =
      ∑ W : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4PhysicalSecondMixedDomainCoefficient
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          s d e t u A W := by
  let sdt := Function.update s d t
  let sue := Function.update sdt e u
  have hsdt :
      ∀ x, ‖((sdt x : ℝ) : ℂ) - 1‖ ≤ (1 : ℝ) :=
    cmp116UpdateRealWeakening_unitShifted s d t ht hs
  have hcapdt :
      ∀ x, ‖((sdt x : ℝ) : ℂ)‖ ≤ Rweak :=
    cmp116UpdateRealWeakening_cap s d t Rweak ht hRweak hcap
  have hsue :
      ∀ x, ‖((sue x : ℝ) : ℂ) - 1‖ ≤ (1 : ℝ) :=
    cmp116UpdateRealWeakening_unitShifted sdt e u hu hsdt
  have hcapsue :
      ∀ x, ‖((sue x : ℝ) : ℂ)‖ ≤ Rweak :=
    cmp116UpdateRealWeakening_cap sdt e u Rweak hu hRweak hcapdt
  have heMem : e ∈ ({e} : Finset (FinBox 4 (2 * Q))) := by simp
  have heMemInsert :
      e ∈ (insert e {d} : Finset (FinBox 4 (2 * Q))) := by simp
  have hHe :
      cmp116SourcePi4RealMixedCovarianceOperatorDerivative
          (R := R) anchor K hc hmass hK sdt ∅ e =
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK sue {e} := by
    rw [cmp116SourcePi4RealMixedCovarianceOperatorDerivative_eq]
    exact
      (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_update_of_mem
        anchor K hc hmass hK sdt {e} e heMem u).symm
  have hHde :
      cmp116SourcePi4RealMixedCovarianceOperatorDerivative
          (R := R) anchor K hc hmass hK sdt {d} e =
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK sue (insert e {d}) := by
    rw [cmp116SourcePi4RealMixedCovarianceOperatorDerivative_eq]
    exact
      (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_update_of_mem
        anchor K hc hmass hK sdt (insert e {d}) e heMemInsert u).symm
  unfold cmp102Eq80SourcePi4SecondMixedDerivativeValue
    cmp102Eq80SourcePi4PhysicalSecondMixedDomainCoefficient
  dsimp only
  rw [cmp116SourcePi4RealMixedCovarianceOperatorCurve_eq,
    cmp116SourcePi4RealMixedCovarianceOperatorCurve_eq,
    hHe, hHde]
  exact
    cmp102Eq80SecondPropagatorMixedDerivative_fullRealMixed_eq_sum_pi4Domains
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sue (insert e {d}) {e} {d}
      hRweak hsue hcapsue hsmall D D₃
      (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK sue ∅)
      Δπ J A
      (fderiv ℝ V₀
        (A -
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK sue ∅ (D A)))
      (fderiv ℝ (fderiv ℝ V₀)
        (A -
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK sue ∅ (D A)))

end

end YangMills.RG
