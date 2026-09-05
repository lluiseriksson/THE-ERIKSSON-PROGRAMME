/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4ConnectedRadialQuadraticSum
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The all-zero weakening leaf belongs to the equation-(80) quadratic sector

The all-zero branch of the weakening FTC tree is not Balaban's residual
`V''_k`.  Weakening and field Taylor expansion are different operations.
This file removes the misleading possibility at the level of the exact
identity: the literal all-zero leaf has the same value/first-order
normalizations as the equation-(80) potential and therefore admits its own
radial Hessian representation in the physical field.

Combining that operator with the already constructed connected-domain
operator gives an exact quadratic representation of the complete
equation-(80) sector.  This is an identity only.  It neither proves the
matrix-element estimate (1.43) for the enlarged operator nor constructs the
independent residual `V''_k` governed by (1.36).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Source-honest name for the all-zero weakening branch.  The older
definition retains `Residual` in its identifier for compatibility, but no
identification with `V''_k` is made. -/
noncomputable def cmp102Eq80SourcePi4FullyDecoupledLeaf
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (A : PhysicalField M Q Nc) : ℝ :=
  cmp102Eq80SourcePi4FullyDecoupledResidual
    (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L A

@[simp] theorem cmp102Eq80SourcePi4FullyDecoupledLeaf_eq_old_name
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (A : PhysicalField M Q Nc) :
    cmp102Eq80SourcePi4FullyDecoupledLeaf
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates s L A =
      cmp102Eq80SourcePi4FullyDecoupledResidual
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates s L A :=
  rfl

/-- `C²` field regularity of the all-zero weakening leaf. -/
theorem contDiff_two_cmp102Eq80SourcePi4FullyDecoupledLeaf
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ 2 D) (hD₃ : ContDiff ℝ 2 D₃)
    (hV₀ : ContDiff ℝ 2 V₀) :
    ContDiff ℝ 2
      (cmp102Eq80SourcePi4FullyDecoupledLeaf
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates s L) := by
  unfold cmp102Eq80SourcePi4FullyDecoupledLeaf
    cmp102Eq80SourcePi4FullyDecoupledResidual
    cmp102Eq80SourcePi4RealPotentialVertexPolynomial
  exact contDiff_two_cmp102Eq80GlobalPotential D D₃ V₀
    (cmp116FiniteMultiaffineInterpolation
      (fun u =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK u ∅)
      base coordinates (cmp116SetRealWeakeningList s L 0))
    Δπ J hD hD₃ hV₀

/-- The all-zero weakening leaf vanishes at zero physical field. -/
theorem cmp102Eq80SourcePi4FullyDecoupledLeaf_zero
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80SourcePi4FullyDecoupledLeaf
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L 0 = 0 := by
  unfold cmp102Eq80SourcePi4FullyDecoupledLeaf
    cmp102Eq80SourcePi4FullyDecoupledResidual
    cmp102Eq80SourcePi4RealPotentialVertexPolynomial
  exact cmp102Eq80GlobalPotential_zero D D₃ V₀ _ Δπ J
    hD0 hD₃0 hV₀0

/-- The all-zero weakening leaf has zero first Fréchet derivative at zero
physical field under the literal equation-(80) component normalizations. -/
theorem cmp102Eq80SourcePi4FullyDecoupledLeaf_hasFDerivAt_zero
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (D' : PhysicalEndomorphism M Q Nc)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD : HasFDerivAt D D' 0)
    (hD₃ : HasFDerivAt D₃ (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀ : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0) :
    HasFDerivAt
      (cmp102Eq80SourcePi4FullyDecoupledLeaf
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates s L)
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0 := by
  unfold cmp102Eq80SourcePi4FullyDecoupledLeaf
    cmp102Eq80SourcePi4FullyDecoupledResidual
    cmp102Eq80SourcePi4RealPotentialVertexPolynomial
  exact cmp102Eq80GlobalPotential_hasFDerivAt_zero
    D D₃ V₀ _ Δπ J D' hD0 hD₃0 hD hD₃ hV₀

/-- Radial Hessian operator of the literal all-zero weakening leaf. -/
noncomputable def cmp102Eq80SourcePi4DecoupledLeafRadialQuadratic
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ 2 D) (hD₃ : ContDiff ℝ 2 D₃)
    (hV₀ : ContDiff ℝ 2 V₀)
    (B : PhysicalField M Q Nc) :
    PhysicalEndomorphism M Q Nc :=
  cmp116Eq142PhysicalRadialQuadratic
    (cmp102Eq80SourcePi4FullyDecoupledLeaf
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L)
    (contDiff_two_cmp102Eq80SourcePi4FullyDecoupledLeaf
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L hD hD₃ hV₀)
    B

/-- Exact field-radial identity for the all-zero weakening leaf. -/
theorem
    inner_cmp102Eq80SourcePi4DecoupledLeafRadialQuadratic_eq_leaf
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ 2 D) (hD₃ : ContDiff ℝ 2 D₃)
    (hV₀ : ContDiff ℝ 2 V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0)
    (hD₃' : HasFDerivAt D₃ (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0)
    (B : PhysicalField M Q Nc) :
    (1 / 2 : ℝ) * inner ℝ B
        (cmp102Eq80SourcePi4DecoupledLeafRadialQuadratic
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          base coordinates s L hD hD₃ hV₀ B B) =
      cmp102Eq80SourcePi4FullyDecoupledLeaf
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates s L B := by
  have hD' : HasFDerivAt D (fderiv ℝ D 0) 0 :=
    (hD.differentiable (by decide)).differentiableAt.hasFDerivAt
  exact inner_cmp116Eq142PhysicalRadialQuadratic_eq_activity
    (cmp102Eq80SourcePi4FullyDecoupledLeaf
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L)
    (contDiff_two_cmp102Eq80SourcePi4FullyDecoupledLeaf
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L hD hD₃ hV₀)
    (cmp102Eq80SourcePi4FullyDecoupledLeaf_zero
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L hD0 hD₃0 hV₀0)
    (cmp102Eq80SourcePi4FullyDecoupledLeaf_hasFDerivAt_zero
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L (fderiv ℝ D 0)
      hD0 hD₃0 hD' hD₃' hV₀').fderiv
    B

/-- Sum of the all-zero-leaf radial operator and the connected-domain radial
operators.  It is the complete exact radial operator for the equation-(80)
sector, without identifying it with Balaban's `Q` before (1.43) is proved. -/
noncomputable def cmp102Eq80SourcePi4CompleteRadialQuadratic
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hs : CMP116RealPhysicalContourRegion Rweak s)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (B : PhysicalField M Q Nc) :
    PhysicalEndomorphism M Q Nc :=
  cmp102Eq80SourcePi4DecoupledLeafRadialQuadratic
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L
      (hD.of_le le_top) (hD₃.of_le le_top) (hV₀.of_le le_top) B +
    cmp102Eq80SourcePi4ConnectedRadialQuadraticSum
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      base coordinates s L hRweak hs hsmall hD hD₃ hV₀ B

set_option maxHeartbeats 128000000 in
/-- The complete literal equation-(80) sector is exactly quadratic in the
physical field with a field-dependent radial operator.  The theorem leaves
no FTC leaf mislabeled as `V''_k`; its remaining analytic obligation is the
source matrix-element estimate (1.43) for this complete operator. -/
theorem cmp102Eq80SourcePi4PhysicalPotential_eq_completeRadialQuadratic
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (hcoordinates : coordinates.Nodup)
    (hcover : ∀ d : FinBox 4 (2 * Q), d ∈ coordinates)
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hRweak : 1 ≤ Rweak)
    (hbaseShift : ∀ x, ‖(base x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hbaseCap : ∀ x, ‖(base x : ℂ)‖ ≤ Rweak)
    (hsShift : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hsCap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hV₀0 : V₀ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0)
    (B : PhysicalField M Q Nc) :
    cmp102Eq80SourcePi4RealMixedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        (cmp116SetRealWeakeningList s L 1) ∅ B =
      (1 / 2 : ℝ) * inner ℝ B
        (cmp102Eq80SourcePi4CompleteRadialQuadratic
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          hAhead hrho hrate PatchCert htri hrange hΔ hΔ1
          base coordinates s L hRweak
          ⟨hsShift, hsCap⟩ hsmall hD hD₃ hV₀ B B) := by
  rw [
    cmp102Eq80SourcePi4PhysicalPotential_eq_decoupledLeaf_add_radialQuadratic
      (R := R) anchor K hc hmass hK
      hAhead hrho hrate hgeom PatchCert htri hrange hΔ hΔ1
      D D₃ V₀ Δπ J base coordinates hcoordinates hcover
      s L hL hRweak hbaseShift hbaseCap hsShift hsCap hsmall
      hD hD₃ hV₀ hD0 hD₃0 hV₀0 hD₃' hV₀' B]
  rw [← cmp102Eq80SourcePi4FullyDecoupledLeaf_eq_old_name]
  rw [← inner_cmp102Eq80SourcePi4DecoupledLeafRadialQuadratic_eq_leaf
    (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
    base coordinates s L
    (hD.of_le le_top) (hD₃.of_le le_top) (hV₀.of_le le_top)
    hD0 hD₃0 hV₀0 hD₃' hV₀' B]
  unfold cmp102Eq80SourcePi4CompleteRadialQuadratic
  rw [ContinuousLinearMap.add_apply, inner_add_right]
  ring

end

end YangMills.RG
