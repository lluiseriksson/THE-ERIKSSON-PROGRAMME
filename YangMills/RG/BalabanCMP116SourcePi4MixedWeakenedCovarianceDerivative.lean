/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexWeakenedCovarianceDerivative

/-!
# Mixed physical weakening derivatives

Repeated FTC requires genuine mixed derivatives, not repeated use of an
unrelated first-derivative interface.  For a finite set `S` of distinct
weakening coordinates, this module differentiates a physical walk monomial
exactly once in every coordinate of `S`: the walk survives precisely when
`S` is contained in its literal active carrier, and the coordinates of `S`
are erased from the remaining monomial.

The terminal recurrence differentiates this source-specific mixed layer in a
new coordinate and obtains the layer indexed by `insert d S`.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The literal mixed derivative of one finite physical covariance layer. -/
noncomputable def
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q))) (n : ℕ) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  fun row col =>
    ∑ head : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
      ∑ tail : ↥(cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged
            physicalBondDist R)
          head n),
        let walk : CMP99AnchoredWalk
            (cmp99PhysicalPatchSuccessorSteps
              (cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q))
              (cmp99SourcePi4ChartCore (M := M))
              cmp99SourcePi4ChartEnlarged
              physicalBondDist R)
            head := ⟨n, tail⟩
        let active := cmp116SourcePi4QuotientWalkActive
          (M := M) anchor head walk
        (if S ⊆ active then
          cmp116ComplexWeakeningMonomial (active \ S) sigma
        else 0) *
          cmp116ComplexPhysicalOperatorCoefficient
            (walk.term
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

/-- The empty mixed derivative is the original physical covariance layer. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_empty
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) (n : ℕ) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma ∅ n =
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK sigma n := by
  classical
  funext row col
  simp [cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative,
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer]

/-- A singleton mixed derivative is exactly the previously constructed
first-derivative layer. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_singleton
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q)) (n : ℕ) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma {d} n =
      cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative
        (R := R) anchor K hc hmass hK sigma d n := by
  classical
  have hdiff : ∀ active : Finset (FinBox 4 (2 * Q)),
      active \ {d} = active.erase d := by
    intro active
    ext x
    simp [and_comm]
  funext row col
  simp [cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative,
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative,
    hdiff]

/-- In a fresh weakening coordinate, the next mixed derivative is the exact
unit finite difference of the current mixed layer.  This is the source-level
multiaffinity identity used to inherit summability without introducing a new
walk majorant. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_insert_eq_sub
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) (hdS : d ∉ S) (n : ℕ) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma (insert d S) n =
      cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
          (R := R) anchor K hc hmass hK
          (Function.update sigma d 1) S n -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
          (R := R) anchor K hc hmass hK
          (Function.update sigma d 0) S n := by
  classical
  funext row col
  unfold cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro head _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro tail _
  let walk : CMP99AnchoredWalk
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R) head :=
    ⟨n, tail⟩
  let active :=
    cmp116SourcePi4QuotientWalkActive (M := M) anchor head walk
  let coefficient : ℂ :=
    cmp116ComplexPhysicalOperatorCoefficient
      (walk.term
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
  change
    (if insert d S ⊆ active then
      cmp116ComplexWeakeningMonomial (active \ insert d S) sigma
    else 0) * coefficient =
      (if S ⊆ active then
        cmp116ComplexWeakeningMonomial (active \ S)
          (Function.update sigma d 1)
      else 0) * coefficient -
      (if S ⊆ active then
        cmp116ComplexWeakeningMonomial (active \ S)
          (Function.update sigma d 0)
      else 0) * coefficient
  by_cases hS : S ⊆ active
  · by_cases hdactive : d ∈ active
    · have hdDiff : d ∈ active \ S := Finset.mem_sdiff.mpr ⟨hdactive, hdS⟩
      have hInsert : insert d S ⊆ active :=
        Finset.insert_subset hdactive hS
      have hErase : (active \ S).erase d = active \ insert d S := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
        tauto
      simp only [hS, hInsert, if_true]
      rw [cmp116ComplexWeakeningMonomial_update_of_mem
          (active \ S) sigma d hdDiff,
        cmp116ComplexWeakeningMonomial_update_of_mem
          (active \ S) sigma d hdDiff, hErase]
      ring
    · have hInsert : ¬ insert d S ⊆ active := by
        intro h
        exact hdactive (h (Finset.mem_insert_self d S))
      have hdDiff : d ∉ active \ S := by
        simp [hdactive]
      simp only [hS, hInsert, if_true, if_false, zero_mul]
      rw [cmp116ComplexWeakeningMonomial_update_of_not_mem
          (active \ S) sigma d hdDiff,
        cmp116ComplexWeakeningMonomial_update_of_not_mem
          (active \ S) sigma d hdDiff]
      ring
  · have hInsert : ¬ insert d S ⊆ active := by
      intro h
      exact hS (Finset.Subset.trans (Finset.subset_insert d S) h)
    simp [hS, hInsert]

/-- Differentiating a mixed physical layer in a fresh coordinate inserts that
coordinate into the mixed-derivative carrier. -/
theorem
    hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_update
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) (hdS : d ∉ S) (n : ℕ)
    (row col : CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
    (t : ℂ) :
    HasDerivAt
      (fun z =>
        cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
          (R := R) anchor K hc hmass hK
          (Function.update sigma d z) S n row col)
      (cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma (insert d S) n row col)
      t := by
  classical
  unfold cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
  apply HasDerivAt.fun_sum
  intro head _
  apply HasDerivAt.fun_sum
  intro tail _
  let walk : CMP99AnchoredWalk
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R) head :=
    ⟨n, tail⟩
  let active :=
    cmp116SourcePi4QuotientWalkActive (M := M) anchor head walk
  let coefficient : ℂ :=
    cmp116ComplexPhysicalOperatorCoefficient
      (walk.term
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
  change HasDerivAt
    (fun z =>
      (if S ⊆ active then
        cmp116ComplexWeakeningMonomial (active \ S)
          (Function.update sigma d z)
      else 0) * coefficient)
    ((if insert d S ⊆ active then
      cmp116ComplexWeakeningMonomial (active \ insert d S) sigma
    else 0) * coefficient) t
  by_cases hS : S ⊆ active
  · by_cases hdactive : d ∈ active
    · have hdDiff : d ∈ active \ S := Finset.mem_sdiff.mpr ⟨hdactive, hdS⟩
      have hInsert : insert d S ⊆ active :=
        Finset.insert_subset hdactive hS
      have hErase : (active \ S).erase d = active \ insert d S := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
        tauto
      simp only [hS, hInsert, if_true]
      simp_rw [cmp116ComplexWeakeningMonomial_update_of_mem
        (active \ S) sigma d hdDiff]
      rw [hErase]
      simpa only [id, one_mul, mul_assoc] using
        (hasDerivAt_id t).mul_const
          (cmp116ComplexWeakeningMonomial
            (active \ insert d S) sigma * coefficient)
    · have hInsert : ¬ insert d S ⊆ active := by
        intro h
        exact hdactive (h (Finset.mem_insert_self d S))
      have hdDiff : d ∉ active \ S := by
        simp [hdactive]
      simp only [hS, hInsert, if_true, if_false, zero_mul]
      simp_rw [cmp116ComplexWeakeningMonomial_update_of_not_mem
        (active \ S) sigma d hdDiff]
      exact hasDerivAt_const t
        (cmp116ComplexWeakeningMonomial (active \ S) sigma * coefficient)
  · have hInsert : ¬ insert d S ⊆ active := by
      intro h
      exact hS (Finset.Subset.trans (Finset.subset_insert d S) h)
    simpa [hS, hInsert] using (hasDerivAt_const t (0 : ℂ))

end

end YangMills.RG
