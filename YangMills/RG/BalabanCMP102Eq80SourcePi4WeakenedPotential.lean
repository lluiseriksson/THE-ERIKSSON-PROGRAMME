/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80GlobalPotential
import YangMills.RG.BalabanCMP116SourcePi4FullWeakenedCovariance

/-!
# The literal equation-(80) potential with the physical source weakening

The complete source `Pi^4` random-walk covariance is inserted here as the
propagator `H(s)` in the four-term CMP102 equation-(80) functional.  Thus the
weakening field no longer parametrizes an abstract propagator.  At full
coupling the potential is definitionally transported to the exact physical
patched covariance.

This is the first source-specific bridge from the constructed random-walk
propagator to the potential that must later be localized into `V_k(Y, ·)`.
It does not yet perform the repeated FTC localization or prove `(1.36)` and
`(1.43)`.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero (M * (2 * Q))] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero (M * (2 * Q))] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Equation (80) with `H(s)` equal to the complete source `Pi^4` weakened
physical covariance constructed from the patched random-walk expansion. -/
noncomputable def cmp102Eq80SourcePi4WeakenedPotential
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (A : PhysicalField M Q Nc) : ℝ :=
  cmp102Eq80GlobalPotential D D₃ V₀
    (cmp116SourcePi4FullWeakenedCovariance
      (R := R) anchor K hc hmass hK s)
    Δπ J A

/-- Full coupling replaces the weakened propagator by the exact physical
patched covariance inside the literal four-term potential. -/
theorem cmp102Eq80SourcePi4WeakenedPotential_one_eq_exact
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc) :
    cmp102Eq80SourcePi4WeakenedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (fun _ => 1) A =
      cmp102Eq80GlobalPotential D D₃ V₀
        (cmp116SourcePi4QuotientExactPatchedCovariance
          K hc hmass hK)
        Δπ J A := by
  unfold cmp102Eq80SourcePi4WeakenedPotential
  rw [cmp116SourcePi4FullWeakenedCovariance_one_eq_exact
    anchor K hsourceRange hrange hc hmass hK hD]

/-- The component normalizations make every weakened potential vanish at
the origin, not only the fully coupled one. -/
theorem cmp102Eq80SourcePi4WeakenedPotential_zero
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80SourcePi4WeakenedPotential
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s 0 = 0 := by
  exact cmp102Eq80GlobalPotential_zero D D₃ V₀
    (cmp116SourcePi4FullWeakenedCovariance
      (R := R) anchor K hc hmass hK s)
    Δπ J hD0 hD₃0 hV₀0

/-- The first derivative in the physical field vanishes at the origin for
every real weakening field. -/
theorem fderiv_cmp102Eq80SourcePi4WeakenedPotential_zero
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (D' : PhysicalEndomorphism M Q Nc)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD : HasFDerivAt D D' 0)
    (hD₃ : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀ : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0) :
    fderiv ℝ
      (cmp102Eq80SourcePi4WeakenedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s) 0 = 0 := by
  exact fderiv_cmp102Eq80GlobalPotential_zero D D₃ V₀
    (cmp116SourcePi4FullWeakenedCovariance
      (R := R) anchor K hc hmass hK s)
    Δπ J D' hD0 hD₃0 hD hD₃ hV₀

/-- `C²` regularity in the physical field is uniform in the choice of the
real weakening parameter. -/
theorem contDiff_two_cmp102Eq80SourcePi4WeakenedPotential
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (hD : ContDiff ℝ 2 D) (hD₃ : ContDiff ℝ 2 D₃)
    (hV₀ : ContDiff ℝ 2 V₀) :
    ContDiff ℝ 2
      (cmp102Eq80SourcePi4WeakenedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s) := by
  exact contDiff_two_cmp102Eq80GlobalPotential D D₃ V₀
    (cmp116SourcePi4FullWeakenedCovariance
      (R := R) anchor K hc hmass hK s)
    Δπ J hD hD₃ hV₀

end

end YangMills.RG
