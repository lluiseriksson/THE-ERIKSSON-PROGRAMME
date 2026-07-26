/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FaaDiBrunoPhysicalInnerJet

/-!
# Physical ordered-partition expansion of equation (80)

Every inner Taylor coefficient in the Faà di Bruno formula is now replaced
by the literal mixed source covariance carried by the coordinates in that
ordered-partition block.  Thus the arbitrary derivative of the complete
four-term equation-(80) potential is an exact finite sum of outer physical
Taylor coefficients evaluated on source-produced mixed propagators.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Physical mixed-derivative carrier attached to one block of an ordered
partition. -/
def cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
    {Q n : ℕ} [NeZero Q]
    (partition : OrderedFinpartition n)
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (block : Fin partition.length) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp116IteratedCoordinateCarrier (partition.partSize block)
    (fun i => coordinates (partition.emb block i)) ∅

/-- An injective global coordinate family remains injective on every ordered
partition block. -/
theorem cmp102Eq80SourcePi4FaaDiBrunoBlockCoordinates_injective
    {D : Type*} {n : ℕ}
    (partition : OrderedFinpartition n)
    (coordinates : Fin n → D)
    (hinjective : Function.Injective coordinates)
    (block : Fin partition.length) :
    Function.Injective
      (fun i : Fin (partition.partSize block) =>
        coordinates (partition.emb block i)) := by
  intro i j hij
  have hemb : partition.emb block i = partition.emb block j :=
    hinjective hij
  have hsigma :
      (⟨block, i⟩ : Σ m, Fin (partition.partSize m)) =
        ⟨block, j⟩ :=
    partition.emb_injective hemb
  cases hsigma
  rfl

/-- Every ordered-partition block therefore satisfies the recursive
freshness condition from the empty carrier. -/
theorem cmp102Eq80SourcePi4FaaDiBrunoBlockCoordinates_fresh
    {D : Type*} [DecidableEq D] {n : ℕ}
    (partition : OrderedFinpartition n)
    (coordinates : Fin n → D)
    (hinjective : Function.Injective coordinates)
    (block : Fin partition.length) :
    CMP116IteratedCoordinatesFresh (partition.partSize block)
      (fun i => coordinates (partition.emb block i)) ∅ := by
  apply cmp116IteratedCoordinatesFresh_of_injective_not_mem
  · exact
      cmp102Eq80SourcePi4FaaDiBrunoBlockCoordinates_injective
        partition coordinates hinjective block
  · intro i
    simp

set_option maxHeartbeats 12000000 in
/-- One inner coefficient in the ordered-partition formula is exactly its
physical mixed covariance. -/
theorem
    ftaylorSeries_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealCovariance_apply_orderedPartitionBlock
    {M Q Nc R Δ n : ℕ}
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hcover : ∀ d : FinBox 4 (2 * Q), d ∈ L)
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (hinjective : Function.Injective coordinates)
    (hRweak : 1 ≤ Rweak)
    (hbase : CMP116RealPhysicalContourRegion Rweak base)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (partition : OrderedFinpartition n)
    (block : Fin partition.length) :
    ftaylorSeries ℝ
        (cmp116FiniteMultiaffineInterpolation
          (fun sigma =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK sigma ∅)
          base L)
        base (partition.partSize block)
        (fun i => Pi.single
          (coordinates (partition.emb block i)) 1) =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK base
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block) := by
  exact
    ftaylorSeries_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealCovariance_apply_coordinateBlock
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
      hrange hΔ hΔ1 base L hL hcover
      (fun i => coordinates (partition.emb block i))
      (cmp102Eq80SourcePi4FaaDiBrunoBlockCoordinates_fresh
        partition coordinates hinjective block)
      hRweak hbase hsmall

set_option maxHeartbeats 16000000 in
/-- Exact physical Faà di Bruno expansion at arbitrary depth.  Every inner
argument of every outer Taylor coefficient is now a literal source mixed
covariance attached to one ordered-partition block. -/
theorem
    iteratedFDeriv_cmp102Eq80SourcePi4RealPotentialVertexPolynomial_apply_coordinateBlock_eq_physicalOrderedPartitions
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hcover : ∀ d : FinBox 4 (2 * Q), d ∈ L)
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (hinjective : Function.Injective coordinates)
    (hRweak : 1 ≤ Rweak)
    (hbase : CMP116RealPhysicalContourRegion Rweak base)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ n V₀) :
    iteratedFDeriv ℝ n
        (fun tau =>
          cmp102Eq80SourcePi4RealPotentialVertexPolynomial
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            base L tau A)
        base (fun i => Pi.single (coordinates i) 1) =
      ∑ partition : OrderedFinpartition n,
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
                partition coordinates block)) := by
  rw [
    iteratedFDeriv_cmp102Eq80SourcePi4RealPotentialVertexPolynomial_apply_eq_sum_orderedFinpartition
      anchor K hc hmass hK D D₃ V₀ Δπ J
      base L base A (fun i => Pi.single (coordinates i) 1) hV₀]
  apply Finset.sum_congr rfl
  intro partition _hpartition
  congr 1
  funext block
  change
    ftaylorSeries ℝ
        (cmp116FiniteMultiaffineInterpolation
          (fun u =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK u ∅)
          base L)
        base (partition.partSize block)
        (fun i => Pi.single
          (coordinates (partition.emb block i)) 1) =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK base
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
  exact
    ftaylorSeries_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealCovariance_apply_orderedPartitionBlock
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
      hrange hΔ hΔ1 base L hL hcover coordinates hinjective hRweak
      hbase hsmall partition block

end

end YangMills.RG
