/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4MixedPotentialFTCExpansionTree
import YangMills.RG.BalabanCMP116SourcePi4RealCovarianceVertexInterpolation

/-!
# Arbitrary-depth physical FTC through the finite vertex polynomial

The complete physical covariance equals a finite multiaffine vertex
polynomial throughout the real weakening region.  Inserting that polynomial
into the literal four-term equation-(80) potential gives a globally smooth
extension.  Its arbitrary-depth FTC tree is therefore valid using only the
actual regularity of `V₀`, and its terminal sum is the literal physical
potential at the coupled endpoint.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- The literal equation-(80) functional evaluated on the globally smooth
finite vertex polynomial of the physical covariance. -/
noncomputable def cmp102Eq80SourcePi4RealPotentialVertexPolynomial
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
    (sigma : FinBox 4 (2 * Q) → ℝ)
    (A : PhysicalField M Q Nc) : ℝ :=
  cmp102Eq80GlobalPotential D D₃ V₀
    (cmp116FiniteMultiaffineInterpolation
      (fun u =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK u ∅)
      base coordinates sigma)
    Δπ J A

/-- The vertex-polynomial equation-(80) extension has exactly the regularity
of `V₀`; the covariance input itself is a finite `C∞` polynomial. -/
theorem contDiff_cmp102Eq80SourcePi4RealPotentialVertexPolynomial
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (n : WithTop ℕ∞)
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
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ n V₀) :
    ContDiff ℝ n
      (fun sigma =>
        cmp102Eq80SourcePi4RealPotentialVertexPolynomial
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          base coordinates sigma A) := by
  unfold cmp102Eq80SourcePi4RealPotentialVertexPolynomial
  exact
    contDiff_cmp102Eq80GlobalPotential_propagatorFamily
      D D₃ V₀
      (cmp116FiniteMultiaffineInterpolation
        (fun u =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK u ∅)
        base coordinates)
      Δπ J A
      (contDiff_cmp116FiniteMultiaffineInterpolation n _ base coordinates)
      hV₀

set_option maxHeartbeats 3000000 in
/-- On the certified real weakening region, the smooth extension is exactly
the literal physical equation-(80) potential. -/
theorem cmp102Eq80SourcePi4RealPotentialVertexPolynomial_eq_physical
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
    (base sigma : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (hcoordinates : coordinates.Nodup)
    (hcover : ∀ d : FinBox 4 (2 * Q), d ∈ coordinates)
    (hRweak : 1 ≤ Rweak)
    (hbaseShift : ∀ x, ‖(base x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hbaseCap : ∀ x, ‖(base x : ℂ)‖ ≤ Rweak)
    (hsigmaShift : ∀ x, ‖(sigma x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hsigmaCap : ∀ x, ‖(sigma x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc) :
    cmp102Eq80SourcePi4RealPotentialVertexPolynomial
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates sigma A =
      cmp102Eq80SourcePi4RealMixedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma ∅ A := by
  unfold cmp102Eq80SourcePi4RealPotentialVertexPolynomial
    cmp102Eq80SourcePi4RealMixedPotential
  rw [cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealCovariance_eq_self
    anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
    hΔ hΔ1 base sigma coordinates hcoordinates hcover hRweak
    hbaseShift hbaseCap hsigmaShift hsigmaCap hsmall]

set_option maxHeartbeats 4000000 in
/-- Along a single fresh weakening coordinate, the smooth vertex extension
and the literal physical equation-(80) potential agree for every real
parameter, not merely on `[0,1]`. -/
theorem cmp102Eq80SourcePi4RealPotentialVertexPolynomial_update_eq_physical
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
    (base s : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (hcoordinates : coordinates.Nodup)
    (hcover : ∀ e : FinBox 4 (2 * Q), e ∈ coordinates)
    (d : FinBox 4 (2 * Q))
    (hRweak : 1 ≤ Rweak)
    (hbaseShift : ∀ x, ‖(base x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hbaseCap : ∀ x, ‖(base x : ℂ)‖ ≤ Rweak)
    (hsShift : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hsCap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc)
    (t : ℝ) :
    cmp102Eq80SourcePi4RealPotentialVertexPolynomial
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates (Function.update s d t) A =
      cmp102Eq80SourcePi4RealMixedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        (Function.update s d t) ∅ A := by
  unfold cmp102Eq80SourcePi4RealPotentialVertexPolynomial
    cmp102Eq80SourcePi4RealMixedPotential
  rw [cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealCovariance_update_eq
    anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
    hΔ hΔ1 base s coordinates hcoordinates hcover d hRweak
    hbaseShift hbaseCap hsShift hsCap hsmall t]

set_option maxHeartbeats 4000000 in
/-- Consequently, the coordinate derivative used by the arbitrary-depth FTC
tree is the genuine derivative of the literal physical potential. -/
theorem
    cmp116RealWeakeningCoordinateDerivative_vertexPolynomial_eq_physical
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
    (base s : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (hcoordinates : coordinates.Nodup)
    (hcover : ∀ e : FinBox 4 (2 * Q), e ∈ coordinates)
    (d : FinBox 4 (2 * Q))
    (hRweak : 1 ≤ Rweak)
    (hbaseShift : ∀ x, ‖(base x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hbaseCap : ∀ x, ‖(base x : ℂ)‖ ≤ Rweak)
    (hsShift : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hsCap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc)
    (t : ℝ) :
    cmp116RealWeakeningCoordinateDerivative
        (fun sigma =>
          cmp102Eq80SourcePi4RealPotentialVertexPolynomial
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            base coordinates sigma A)
        d t s =
      cmp116RealWeakeningCoordinateDerivative
        (fun sigma =>
          cmp102Eq80SourcePi4RealMixedPotential
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            sigma ∅ A)
        d t s := by
  unfold cmp116RealWeakeningCoordinateDerivative
  congr 1
  funext u
  exact
    cmp102Eq80SourcePi4RealPotentialVertexPolynomial_update_eq_physical
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 D D₃ V₀ Δπ J base s coordinates hcoordinates hcover d
      hRweak hbaseShift hbaseCap hsShift hsCap hsmall A u

/-- Setting any finite list of coordinates to one preserves the physical
unit-shift contour. -/
theorem cmp116SetRealWeakeningList_unitShifted_one
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (L : List D)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖(cmp116SetRealWeakeningList s L 1 x : ℂ) - 1‖ ≤
      (1 : ℝ) := by
  intro x
  by_cases hx : x ∈ L
  · simp [cmp116SetRealWeakeningList, hx]
  · simpa [cmp116SetRealWeakeningList, hx] using hs x

/-- The same coupled endpoint preserves the physical absolute cap whenever
`Rweak ≥ 1`. -/
theorem cmp116SetRealWeakeningList_cap_one
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (L : List D) (Rweak : ℝ)
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak) :
    ∀ x, ‖(cmp116SetRealWeakeningList s L 1 x : ℂ)‖ ≤ Rweak := by
  intro x
  by_cases hx : x ∈ L
  · simpa [cmp116SetRealWeakeningList, hx] using hRweak
  · simpa [cmp116SetRealWeakeningList, hx] using hs x

/-- Arbitrary-depth FTC tree of the finite physical vertex-polynomial
extension. -/
noncomputable def cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree
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
    CMP116FTCExpansionTree ℝ L.length :=
  cmp116RealWeakeningFTCExpansionTree
    (fun sigma =>
      cmp102Eq80SourcePi4RealPotentialVertexPolynomial
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates sigma A)
    s L

/-- The arbitrary-depth vertex-polynomial FTC tree is valid from the actual
regularity of `V₀`, with no `ContDiff` premise on the weakened potential. -/
theorem cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree_valid
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
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ (L.length + 1) V₀) :
    (cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L A).Valid := by
  unfold cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree
  exact
    cmp116RealWeakeningFTCExpansionTree_valid _ s L hL
      (contDiff_cmp102Eq80SourcePi4RealPotentialVertexPolynomial
        (L.length + 1) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates A hV₀)

set_option maxHeartbeats 4000000 in
/-- The valid arbitrary-depth FTC expansion sums to the literal physical
equation-(80) potential at the fully coupled endpoint. -/
theorem
    cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree_expansionSum_eq_physical
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
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ (L.length + 1) V₀) :
    (cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates s L A).expansionSum =
      cmp102Eq80SourcePi4RealMixedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        (cmp116SetRealWeakeningList s L 1) ∅ A := by
  have hvalid :=
    cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree_valid
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L hL A hV₀
  calc
    _ = (cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          base coordinates s L A).coupledEndpoint :=
      CMP116FTCExpansionTree.expansionSum_eq_coupledEndpoint _ hvalid
    _ = cmp102Eq80SourcePi4RealPotentialVertexPolynomial
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          base coordinates (cmp116SetRealWeakeningList s L 1) A := by
      exact
        cmp116RealWeakeningFTCExpansionTree_coupledEndpoint
          _ s L hL
    _ = _ :=
      cmp102Eq80SourcePi4RealPotentialVertexPolynomial_eq_physical
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
        hrange hΔ hΔ1 D D₃ V₀ Δπ J base
        (cmp116SetRealWeakeningList s L 1) coordinates hcoordinates
        hcover hRweak hbaseShift hbaseCap
        (cmp116SetRealWeakeningList_unitShifted_one s L hsShift)
        (cmp116SetRealWeakeningList_cap_one s L Rweak hRweak hsCap)
        hsmall A

end

end YangMills.RG
