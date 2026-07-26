/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FaaDiBrunoPhysicalExpansion
import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredPotentialDerivative

/-!
# Domain localization of the physical Faà di Bruno expansion

Each mixed propagator in an ordered-partition block is decomposed into its
finite sum of physical source-domain operators.  Multilinearity of the outer
Taylor coefficient expands this exactly over choices of one source domain
per block.  The choices are then regrouped by the connected-candidate label
given by their union with the common literal `Pi^4` anchor.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- One choice of a physical source domain for every block of an ordered
partition. -/
abbrev CMP102Eq80FaaDiBrunoDomainChoice
    {Q n : ℕ} (partition : OrderedFinpartition n) :=
  Fin partition.length → Finset (FinBox 4 (2 * Q))

/-- One domain-choice term in the physical ordered-partition expansion. -/
noncomputable def cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTerm
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
    (base : FinBox 4 (2 * Q) → ℝ)
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
        base L base)
      partition.length
    (fun block =>
      cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
        (R := R) anchor K hc hmass hK base
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
        (choice block))

/-- Coefficient of one union label inside one ordered partition. -/
noncomputable def cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficient
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
    (base : FinBox 4 (2 * Q) → ℝ)
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
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTerm
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
      base L coordinates partition choice

set_option maxHeartbeats 16000000 in
/-- Multilinearity expands one physical ordered-partition term into the
finite sum over choices of one connected-candidate source domain per block.
-/
theorem cmp102Eq80SourcePi4FaaDiBruno_partitionTerm_eq_sum_domainChoices
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (hRweak : 1 ≤ Rweak)
    (hbase : CMP116RealPhysicalContourRegion Rweak base)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ftaylorSeries ℝ
        (cmp102Eq80PotentialAsFunctionOfPropagator
          D D₃ V₀ Δπ J A)
        (cmp116FiniteMultiaffineInterpolation
          (fun u =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK u ∅)
          base L base)
        partition.length
      (fun block =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK base
          (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
            partition coordinates block)) =
      ∑ choice : CMP102Eq80FaaDiBrunoDomainChoice
          (Q := Q) partition,
        cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTerm
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          base L coordinates partition choice := by
  let T :=
    ftaylorSeries ℝ
      (cmp102Eq80PotentialAsFunctionOfPropagator
        D D₃ V₀ Δπ J A)
      (cmp116FiniteMultiaffineInterpolation
        (fun u =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK u ∅)
        base L base)
      partition.length
  let term := fun
      (block : Fin partition.length)
      (Y : Finset (FinBox 4 (2 * Q))) =>
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
      (R := R) anchor K hc hmass hK base
      (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
        partition coordinates block) Y
  have hblocks :
      (fun block =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK base
          (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
            partition coordinates block)) =
        fun block => ∑ Y, term block Y := by
    funext block
    exact
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 base
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
        hRweak hbase.1 hbase.2 hsmall
  rw [hblocks]
  have hmap :=
    T.map_sum_finset term
      (fun _ => (Finset.univ :
        Finset (Finset (FinBox 4 (2 * Q)))))
  simpa [T, term,
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTerm] using hmap

/-- Exact regrouping of the domain choices of one ordered partition by their
anchored union label. -/
theorem sum_cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficient
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n) :
    (∑ choice : CMP102Eq80FaaDiBrunoDomainChoice
        (Q := Q) partition,
      cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTerm
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        base L coordinates partition choice) =
      ∑ W : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficient
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          base L coordinates partition W := by
  classical
  unfold cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficient
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
      (f := cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTerm
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        base L coordinates partition)
      (fun _ _ => Finset.mem_univ _)).symm

end

end YangMills.RG
