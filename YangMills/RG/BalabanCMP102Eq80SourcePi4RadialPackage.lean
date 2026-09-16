/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4DecoupledLeafRadial

/-!
# Packaged physical data for the equation-(80) radial sector

The source-faithful equation-(80) theorem has a deliberately explicit
signature.  Repeating that signature in every subsequent jet estimate is
both fragile and expensive for the elaborator.  This file packages the same
data and certificates once, then exposes the literal potential, its complete
radial operator, and the exact quadratic identity through short projections.

This is only an interface compression.  It adds no analytic estimate and
does not identify the radial residual with Balaban's `V''_k` or prove (1.36).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private abbrev PackField (M Q Nc : ℕ) [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PackEndomorphism (M Q Nc : ℕ) [NeZero M] [NeZero Q] :=
  PackField M Q Nc →L[ℝ] PackField M Q Nc

/-- All physical data and certificates consumed by the exact equation-(80)
radial identity.  Keeping them in one dependent record prevents subsequent
third-jet statements from duplicating the full source theorem signature. -/
structure CMP102Eq80SourcePi4RadialPackage
    (M Q Nc R Δ : ℕ)
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)] where
  anchor : FinBox 4 Q
  K : PackEndomorphism M Q Nc
  c : ℝ
  mass : ℝ
  hc : 0 < c
  hmass : 0 < mass
  hK : IsCoerciveCLM K c
  Ahead : ℝ
  rho : ℝ
  rate : ℝ
  Rweak : ℝ
  hAhead : 0 ≤ Ahead
  hrho : 0 ≤ rho
  hrate : 0 < rate
  hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1
  patchCert : CMP99PhysicalPatchWeightedCertificate
    (cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))
    K cmp99SourcePi4ChartEnlarged
    (cmp99SourcePi4ChartCore (M := M))
    hc hmass hK physicalBondDist Ahead rho rate
  htri : ∀ target source middle :
    PhysicalBond 4 (M * (2 * Q)),
    physicalBondDist target source ≤
      physicalBondDist target middle + physicalBondDist middle source
  hrange : R + 1 ≤ 4 * M
  hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ
  hΔ1 : 1 ≤ Δ
  D : PackField M Q Nc → PackField M Q Nc
  D₃ : PackField M Q Nc → PackField M Q Nc
  V₀ : PackField M Q Nc → ℝ
  Δπ : PackEndomorphism M Q Nc
  J : PackField M Q Nc
  base : FinBox 4 (2 * Q) → ℝ
  coordinates : List (FinBox 4 (2 * Q))
  hcoordinates : coordinates.Nodup
  hcover : ∀ d : FinBox 4 (2 * Q), d ∈ coordinates
  s : FinBox 4 (2 * Q) → ℝ
  L : List (FinBox 4 (2 * Q))
  hL : L.Nodup
  hRweak : 1 ≤ Rweak
  hbaseShift : ∀ x, ‖(base x : ℂ) - 1‖ ≤ (1 : ℝ)
  hbaseCap : ∀ x, ‖(base x : ℂ)‖ ≤ Rweak
  hsShift : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ)
  hsCap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak
  hsmall : ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1
  hD : ContDiff ℝ ⊤ D
  hD₃ : ContDiff ℝ ⊤ D₃
  hV₀ : ContDiff ℝ ⊤ V₀
  hD0 : D 0 = 0
  hD₃0 : D₃ 0 = 0
  hV₀0 : V₀ 0 = 0
  hD₃' : HasFDerivAt D₃ (0 : PackEndomorphism M Q Nc) 0
  hV₀' : HasFDerivAt V₀ (0 : PackField M Q Nc →L[ℝ] ℝ) 0

namespace CMP102Eq80SourcePi4RadialPackage

/-- The literal real equation-(80) potential selected by the package. -/
noncomputable def physicalPotential
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (P : CMP102Eq80SourcePi4RadialPackage M Q Nc R Δ)
    (B : PackField M Q Nc) : ℝ :=
  cmp102Eq80SourcePi4RealMixedPotential
    (R := R) P.anchor P.K P.hc P.hmass P.hK
    P.D P.D₃ P.V₀ P.Δπ P.J
    (cmp116SetRealWeakeningList P.s P.L 1) ∅ B

/-- The complete field-dependent radial operator selected by the package. -/
noncomputable def radialOperator
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (P : CMP102Eq80SourcePi4RadialPackage M Q Nc R Δ)
    (B : PackField M Q Nc) : PackEndomorphism M Q Nc :=
  cmp102Eq80SourcePi4CompleteRadialQuadratic
    (R := R) P.anchor P.K P.hc P.hmass P.hK
    P.D P.D₃ P.V₀ P.Δπ P.J
    P.hAhead P.hrho P.hrate P.patchCert P.htri P.hrange P.hΔ P.hΔ1
    P.base P.coordinates P.s P.L P.hRweak
    ⟨P.hsShift, P.hsCap⟩ P.hsmall P.hD P.hD₃ P.hV₀ B

set_option maxHeartbeats 128000000 in
/-- Packaged form of the exact source-faithful equation-(80) radial identity. -/
theorem physicalPotential_eq_half_inner_radialOperator
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (P : CMP102Eq80SourcePi4RadialPackage M Q Nc R Δ)
    (B : PackField M Q Nc) :
    P.physicalPotential B =
      (1 / 2 : ℝ) * inner ℝ B (P.radialOperator B B) := by
  exact cmp102Eq80SourcePi4PhysicalPotential_eq_completeRadialQuadratic
    (R := R) P.anchor P.K P.hc P.hmass P.hK
    P.hAhead P.hrho P.hrate P.hgeom P.patchCert P.htri P.hrange P.hΔ P.hΔ1
    P.D P.D₃ P.V₀ P.Δπ P.J
    P.base P.coordinates P.hcoordinates P.hcover
    P.s P.L P.hL P.hRweak
    P.hbaseShift P.hbaseCap P.hsShift P.hsCap P.hsmall
    P.hD P.hD₃ P.hV₀ P.hD0 P.hD₃0 P.hV₀0 P.hD₃' P.hV₀' B

end CMP102Eq80SourcePi4RadialPackage

end

end YangMills.RG
