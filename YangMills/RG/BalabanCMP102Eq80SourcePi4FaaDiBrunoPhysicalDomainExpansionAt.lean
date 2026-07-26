/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FaaDiBrunoPhysicalDomainExpansion

/-!
# Physical domain expansion at a variable contour point

The vertex interpolant used to represent the physical covariance has one
fixed certified base.  The FTC tree, however, evaluates its derivatives at
many other certified contour points.  This module separates those two
arguments throughout the physical domain expansion.

No domain is called `V_k(Y, ·)` here.  The result is the exact localized jet
which will be integrated by the source FTC construction before that final
dictionary is claimed.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- One physical domain-choice term at a contour point `sigma`, with the
finite vertex polynomial based independently at `vertexBase`. -/
noncomputable def cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (choice : CMP102Eq80FaaDiBrunoDomainChoice
      (Q := Q) partition) : ℝ :=
  ftaylorSeries ℝ
      (cmp102Eq80PotentialAsFunctionOfPropagator
        D D₃ V₀ Δπ J A)
      (cmp116FiniteMultiaffineInterpolation
        (fun u =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK u ∅)
        vertexBase L sigma)
      partition.length
    (fun block =>
      cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
        (R := R) anchor K hc hmass hK sigma
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
        (choice block))

/-- Coefficient of one union label inside one ordered partition, evaluated
at the variable contour point. -/
noncomputable def
    cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (W : Finset (FinBox 4 (2 * Q))) : ℝ :=
  ∑ choice ∈
      (Finset.univ :
        Finset (CMP102Eq80FaaDiBrunoDomainChoice
          (Q := Q) partition)).filter
        (fun choice =>
          cmp102Eq80SourcePi4AnchoredDomainUnion anchor
            Finset.univ choice = W),
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
      vertexBase sigma L coordinates partition choice

/-- Complete arbitrary-depth coefficient of one physical union label at a
variable contour point. -/
noncomputable def cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (W : Finset (FinBox 4 (2 * Q))) : ℝ :=
  ∑ partition : OrderedFinpartition n,
    cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
      vertexBase sigma L coordinates partition W

set_option maxHeartbeats 16000000 in
/-- Multilinearity expands one physical ordered-partition term at `sigma`
into its exact finite sum over source-domain choices. -/
theorem
    cmp102Eq80SourcePi4FaaDiBruno_partitionTermAt_eq_sum_domainChoices
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
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
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (hRweak : 1 ≤ Rweak)
    (hsigma : CMP116RealPhysicalContourRegion Rweak sigma)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ftaylorSeries ℝ
        (cmp102Eq80PotentialAsFunctionOfPropagator
          D D₃ V₀ Δπ J A)
        (cmp116FiniteMultiaffineInterpolation
          (fun u =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK u ∅)
          vertexBase L sigma)
        partition.length
      (fun block =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK sigma
          (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
            partition coordinates block)) =
      ∑ choice : CMP102Eq80FaaDiBrunoDomainChoice
          (Q := Q) partition,
        cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma L coordinates partition choice := by
  let T :=
    ftaylorSeries ℝ
      (cmp102Eq80PotentialAsFunctionOfPropagator
        D D₃ V₀ Δπ J A)
      (cmp116FiniteMultiaffineInterpolation
        (fun u =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK u ∅)
        vertexBase L sigma)
      partition.length
  let term := fun
      (block : Fin partition.length)
      (Y : Finset (FinBox 4 (2 * Q))) =>
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
      (R := R) anchor K hc hmass hK sigma
      (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
        partition coordinates block) Y
  have hblocks :
      (fun block =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK sigma
          (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
            partition coordinates block)) =
        fun block => ∑ Y, term block Y := by
    funext block
    exact
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 sigma
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
        hRweak hsigma.1 hsigma.2 hsmall
  rw [hblocks]
  have hmap :=
    T.map_sum_finset term
      (fun _ => (Finset.univ :
        Finset (Finset (FinBox 4 (2 * Q)))))
  simpa [T, term,
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt] using hmap

/-- Exact regrouping of the variable-point domain choices of one ordered
partition by their anchored union label. -/
theorem
    sum_cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n) :
    (∑ choice : CMP102Eq80FaaDiBrunoDomainChoice
        (Q := Q) partition,
      cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates partition choice) =
      ∑ W : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma L coordinates partition W := by
  classical
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
  exact
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ :
        Finset (CMP102Eq80FaaDiBrunoDomainChoice
          (Q := Q) partition)))
      (t := (Finset.univ :
        Finset (Finset (FinBox 4 (2 * Q)))))
      (g := fun choice =>
        cmp102Eq80SourcePi4AnchoredDomainUnion anchor
          Finset.univ choice)
      (f := cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates partition)
      (fun _ _ => Finset.mem_univ _)).symm

set_option maxHeartbeats 24000000 in
/-- Complete arbitrary-depth equation-(80) jet at a variable contour point,
localized exactly by physical source-domain union labels. -/
theorem
    iteratedFDeriv_cmp102Eq80SourcePi4RealPotentialVertexPolynomial_apply_coordinateBlock_at_eq_sum_physicalDomains
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
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
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hcover : ∀ d : FinBox 4 (2 * Q), d ∈ L)
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (hinjective : Function.Injective coordinates)
    (hRweak : 1 ≤ Rweak)
    (hvertexBase : CMP116RealPhysicalContourRegion Rweak vertexBase)
    (hsigma : CMP116RealPhysicalContourRegion Rweak sigma)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ n V₀) :
    iteratedFDeriv ℝ n
        (fun tau =>
          cmp102Eq80SourcePi4RealPotentialVertexPolynomial
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            vertexBase L tau A)
        sigma (fun i => Pi.single (coordinates i) 1) =
      ∑ W : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma L coordinates W := by
  rw [
    iteratedFDeriv_cmp102Eq80SourcePi4RealPotentialVertexPolynomial_apply_coordinateBlock_at_eq_physicalOrderedPartitions
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      vertexBase sigma L hL hcover coordinates hinjective hRweak
      hvertexBase hsigma hsmall hV₀]
  simp_rw [
    cmp102Eq80SourcePi4FaaDiBruno_partitionTermAt_eq_sum_domainChoices
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      vertexBase sigma L coordinates _ hRweak hsigma hsmall]
  simp_rw [
    sum_cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      vertexBase sigma L coordinates]
  rw [Finset.sum_comm]
  rfl

end

end YangMills.RG
