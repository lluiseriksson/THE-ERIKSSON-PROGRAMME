/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4DerivativeLayerLocalization
import YangMills.RG.BalabanCMP116SourcePi4MixedWeakenedCovarianceDerivative

/-!
# Connected localization of a physical mixed derivative layer

The singleton derivative regrouping is extended to a literal finite mixed
carrier `S`.  A surviving physical walk must contain every coordinate of
`S`; a chosen `root ∈ S` therefore gives a canonical face-connected domain
for that term.  The theorem below is an exact finite regrouping of the source
walk formula, not a postulated domain decomposition.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Literal scalar contribution of one physical walk to a mixed derivative
layer.  It survives precisely when its active carrier contains `S`. -/
noncomputable def cmp116SourcePi4MixedDerivativeLayerWalkTerm
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n) : ℂ :=
  let active := cmp116SourcePi4LayerWalkActive anchor idx
  (if S ⊆ active then
    cmp116ComplexWeakeningMonomial (active \ S) sigma
  else 0) *
    cmp116ComplexPhysicalOperatorCoefficient
      (idx.walk.term
        (cmp99PhysicalPatchHead
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK))
      col.1 row.1 col.2 row.2

/-- A surviving mixed walk term contains every differentiated coordinate in
its literal active carrier. -/
theorem cmp116SourcePi4MixedDerivativeLayerWalkTerm_eq_zero_of_not_subset
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n)
    (hS : ¬S ⊆ cmp116SourcePi4LayerWalkActive anchor idx) :
    cmp116SourcePi4MixedDerivativeLayerWalkTerm
      anchor K hc hmass hK sigma S row col idx = 0 := by
  simp [cmp116SourcePi4MixedDerivativeLayerWalkTerm, hS]

/-- In particular, every chosen root of the mixed carrier lies in the active
carrier of a nonzero source term. -/
theorem cmp116SourcePi4MixedDerivativeLayerWalkTerm_root_mem_active
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q)) (hroot : root ∈ S)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n)
    (hterm : cmp116SourcePi4MixedDerivativeLayerWalkTerm
      anchor K hc hmass hK sigma S row col idx ≠ 0) :
    root ∈ cmp116SourcePi4LayerWalkActive anchor idx := by
  by_contra hnot
  apply hterm
  apply cmp116SourcePi4MixedDerivativeLayerWalkTerm_eq_zero_of_not_subset
  intro hS
  exact hnot (hS hroot)

/-- Hence the canonical connected domain of a nonzero mixed term contains no
coordinate outside that term's literal active carrier. -/
theorem cmp116SourcePi4MixedDerivativeAnchoredDomain_subset_active
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q)) (hroot : root ∈ S)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n)
    (hterm : cmp116SourcePi4MixedDerivativeLayerWalkTerm
      anchor K hc hmass hK sigma S row col idx ≠ 0) :
    cmp116AnchoredLocalizationDomain
        (cmp116CoarseFaceAdj 4 (2 * Q))
        (fun _ : CMP116SourcePi4LayerWalkIndex M Q R n => root)
        (cmp116SourcePi4LayerWalkActive anchor) idx ⊆
      cmp116SourcePi4LayerWalkActive anchor idx := by
  have hr :=
    cmp116SourcePi4MixedDerivativeLayerWalkTerm_root_mem_active
      anchor K hc hmass hK sigma S root hroot row col idx hterm
  simpa [Finset.insert_eq_of_mem hr] using
    (cmp116AnchoredLocalizationDomain_subset
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (fun _ : CMP116SourcePi4LayerWalkIndex M Q R n => root)
      (cmp116SourcePi4LayerWalkActive anchor) idx)

/-- One literal physical mixed derivative layer is exactly the sum of its
walk coefficients grouped by the canonical connected component containing a
chosen coordinate of the mixed carrier. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_eq_sum_anchoredFiber
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q)) (_hroot : root ∈ S)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma S n row col =
      ∑ Y ∈ cmp116AnchoredLocalizationDomains
          (cmp116CoarseFaceAdj 4 (2 * Q))
          (Finset.univ :
            Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
          (fun _ => root)
          (cmp116SourcePi4LayerWalkActive anchor),
        cmp116AnchoredFiberCoefficient
          (cmp116CoarseFaceAdj 4 (2 * Q))
          (Finset.univ :
            Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
          (fun _ => root)
          (cmp116SourcePi4LayerWalkActive anchor)
          (cmp116SourcePi4MixedDerivativeLayerWalkTerm
            anchor K hc hmass hK sigma S row col) Y := by
  classical
  have hregroup :=
    cmp116_sum_eq_sum_anchoredFiberCoefficient
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (Finset.univ :
        Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
      (fun _ => root)
      (cmp116SourcePi4LayerWalkActive anchor)
      (cmp116SourcePi4MixedDerivativeLayerWalkTerm
        anchor K hc hmass hK sigma S row col)
  rw [Fintype.sum_sigma] at hregroup
  simpa [cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative,
    cmp116SourcePi4MixedDerivativeLayerWalkTerm,
    cmp116SourcePi4LayerWalkActive,
    CMP116SourcePi4LayerWalkIndex.walk] using hregroup

/-- The same physical regrouping over the fixed universal finite family of
all domains.  Coefficients of domains absent from the layer are definitionally
empty fiber sums.  A fixed target family is the form needed to interchange
the later walk-length sum with localization. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_eq_sum_univ_anchoredFiber
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q)) (_hroot : root ∈ S)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma S n row col =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp116AnchoredFiberCoefficient
          (cmp116CoarseFaceAdj 4 (2 * Q))
          (Finset.univ :
            Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
          (fun _ => root)
          (cmp116SourcePi4LayerWalkActive anchor)
          (cmp116SourcePi4MixedDerivativeLayerWalkTerm
            anchor K hc hmass hK sigma S row col) Y := by
  classical
  have hregroup :
      (∑ idx : CMP116SourcePi4LayerWalkIndex M Q R n,
          cmp116SourcePi4MixedDerivativeLayerWalkTerm
            anchor K hc hmass hK sigma S row col idx) =
        ∑ Y : Finset (FinBox 4 (2 * Q)),
          cmp116AnchoredFiberCoefficient
            (cmp116CoarseFaceAdj 4 (2 * Q))
            (Finset.univ :
              Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
            (fun _ => root)
            (cmp116SourcePi4LayerWalkActive anchor)
            (cmp116SourcePi4MixedDerivativeLayerWalkTerm
              anchor K hc hmass hK sigma S row col) Y := by
    exact (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ :
        Finset (CMP116SourcePi4LayerWalkIndex M Q R n)))
      (t := (Finset.univ : Finset (Finset (FinBox 4 (2 * Q)))))
      (g := cmp116AnchoredLocalizationDomain
        (cmp116CoarseFaceAdj 4 (2 * Q))
        (fun _ : CMP116SourcePi4LayerWalkIndex M Q R n => root)
        (cmp116SourcePi4LayerWalkActive anchor))
      (fun _ _ => Finset.mem_univ _)
      (cmp116SourcePi4MixedDerivativeLayerWalkTerm
        anchor K hc hmass hK sigma S row col)).symm
  rw [Fintype.sum_sigma] at hregroup
  simpa [cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative,
    cmp116SourcePi4MixedDerivativeLayerWalkTerm,
    cmp116SourcePi4LayerWalkActive,
    CMP116SourcePi4LayerWalkIndex.walk] using hregroup

end

end YangMills.RG
