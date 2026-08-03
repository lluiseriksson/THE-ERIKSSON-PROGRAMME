/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma1WeakenedPropagatorBound
import YangMills.RG.BalabanCMP99ComplexFineHeadTailWordExpansion

/-!
# Physical covariance specialization of CMP116 Lemma 1 L1

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations are not yet compiler-verified.

The generic L1 certificate constructs a weakened series over one walk type.
The literal source-Pi4 covariance is stored entrywise as a length `tsum`
whose fibres are finite dependent types of physical walks.  This module
supplies the exact dependent reindexing

`Sigma length, CMP99SourcePi4FineWalkIndex M Q R length`

and proves that the entrywise internally constructed L1 propagator is the
literal complex covariance
`cmp116SourcePi4FullComplexWeakenedCovarianceMatrix`.  One common
`treeLength`, `baseWeight`, and scalar budget is required for every matrix
entry.  This matches the entrywise construction and estimates of the
physical walk matrix without imposing an artificial complex normed-space
structure on the repository's operator-norm matrix representation.  The
exchange of the sigma sum with the length/fibre sums uses the radial
summability already carried by each scalar L1 certificate; no conditionally
convergent rearrangement is made.

Honest scope: this is the physical `G(s)` bridge only.  The current literal
`H(s)` expansion multiplies several sigma-dependent fine-walk factors, so it
does not factor through the square-free active `Finset` used here without an
additional multiplicity-aware expansion.  No `H0(s)` producer is supplied.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

/-- One literal physical covariance walk, with its length retained as the
outer sigma coordinate. -/
abbrev CMP116Lemma1PhysicalCovarianceWalk
    (M Q R : ℕ) [NeZero M] [NeZero Q] :=
  Σ length : ℕ, CMP99SourcePi4FineWalkIndex M Q R length

/-- Exact weakening carrier of a physical covariance walk. -/
noncomputable def cmp116Lemma1PhysicalCovarianceWalkActive
    {M Q R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (walk : CMP116Lemma1PhysicalCovarianceWalk M Q R) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp99SourcePi4FineWalkIndex.active anchor walk.2

/-- Sigma-independent physical operator carried by one covariance walk. -/
noncomputable def cmp116Lemma1PhysicalCovarianceWalkTerm
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (walk : CMP116Lemma1PhysicalCovarianceWalk M Q R) :
    Matrix (FineCoord M Q Nc) (FineCoord M Q Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix
    (cmp99SourcePi4FineWalkIndex.operator K hc hmass hK walk.2)

/-- One scalar entry of the sigma-independent physical walk operator.  The
physical covariance is constructed entrywise, and `ℂ` carries the canonical
complex normed-space structure required by generic L1. -/
noncomputable def cmp116Lemma1PhysicalCovarianceWalkEntryTerm
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (row col : FineCoord M Q Nc)
    (walk : CMP116Lemma1PhysicalCovarianceWalk M Q R) : ℂ :=
  cmp116Lemma1PhysicalCovarianceWalkTerm K hc hmass hK walk row col

/-- One term of the generic weakened series is definitionally the literal
physical fine-walk term. -/
theorem cmp116Lemma1PhysicalCovarianceWalkTerm_eq
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (walk : CMP116Lemma1PhysicalCovarianceWalk M Q R) :
    cmp116ComplexWeakeningMonomial
        (cmp116Lemma1PhysicalCovarianceWalkActive anchor walk) sigma •
      cmp116Lemma1PhysicalCovarianceWalkTerm K hc hmass hK walk =
    cmp99SourcePi4ComplexFineWalkTerm
      anchor K hc hmass hK sigma walk.2 := by
  rfl

/-- Matrix assembled from the scalar L1 propagators with a uniform source
budget over all row/column pairs. -/
noncomputable def cmp116Lemma1PhysicalCovariancePropagator
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {treeLength : CMP116Lemma1PhysicalCovarianceWalk M Q R → ℕ}
    {baseWeight : CMP116Lemma1PhysicalCovarianceWalk M Q R → ℝ}
    {B0 delta0 delta1 kappa1 : ℝ}
    (C : ∀ row col,
      CMP116Lemma1WeakenedPropagatorCertificate
        (cmp116Lemma1PhysicalCovarianceWalkActive anchor)
        (cmp116Lemma1PhysicalCovarianceWalkEntryTerm
          K hc hmass hK row col)
        treeLength baseWeight B0 delta0 delta1 (M : ℝ) kappa1)
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix (FineCoord M Q Nc) (FineCoord M Q Nc) ℂ :=
  fun row col => (C row col).propagator sigma

/-- The generic L1 propagator specialized to the dependent physical walk
index is exactly the literal source-Pi4 complex covariance `G(s)`.

The certificate family shares one source budget across all entries.  No
separate covariance convergence hypothesis is needed: the physical matrix is
definitionally the entrywise length `tsum`, and the L1 radial majorant is what
justifies the sole dependent reindexing. -/
theorem cmp116Lemma1PhysicalCovariancePropagator_eq
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    {treeLength : CMP116Lemma1PhysicalCovarianceWalk M Q R → ℕ}
    {baseWeight : CMP116Lemma1PhysicalCovarianceWalk M Q R → ℝ}
    {B0 delta0 delta1 kappa1 : ℝ}
    (C : ∀ row col,
      CMP116Lemma1WeakenedPropagatorCertificate
        (cmp116Lemma1PhysicalCovarianceWalkActive anchor)
        (cmp116Lemma1PhysicalCovarianceWalkEntryTerm
          K hc hmass hK row col)
        treeLength baseWeight B0 delta0 delta1 (M : ℝ) kappa1)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1) :
    cmp116Lemma1PhysicalCovariancePropagator
        anchor K hc hmass hK C sigma =
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma := by
  classical
  ext row col
  let shiftedRadius : FinBox 4 (2 * Q) → ℝ :=
    fun _ => Real.exp kappa1 - 1
  have hR : 1 ≤ Real.exp kappa1 :=
    Real.one_le_exp (C row col).kappa1_nonneg
  have hsigmaShifted :
      sigma ∈ cmp116ComplexShiftedWeakeningPolydisc shiftedRadius := by
    intro d
    simpa [shiftedRadius] using hsigma d
  have hwalkCap :
      ∀ (walk : CMP116Lemma1PhysicalCovarianceWalk M Q R)
        (d : FinBox 4 (2 * Q)),
      d ∈ cmp116Lemma1PhysicalCovarianceWalkActive
          (M := M) (Q := Q) (R := R) anchor walk →
        1 + shiftedRadius d ≤ Real.exp kappa1 := by
    intro walk d _hd
    simp [shiftedRadius]
  have hflat : Summable fun walk :
      CMP116Lemma1PhysicalCovarianceWalk M Q R =>
        cmp116ComplexWeakeningMonomial
            (cmp116Lemma1PhysicalCovarianceWalkActive anchor walk) sigma •
          cmp116Lemma1PhysicalCovarianceWalkEntryTerm
            K hc hmass hK row col walk :=
    summable_cmp116ComplexWeakenedRandomWalkSeries
      (cmp116Lemma1PhysicalCovarianceWalkActive anchor)
      (cmp116Lemma1PhysicalCovarianceWalkEntryTerm
        K hc hmass hK row col)
      sigma shiftedRadius (Real.exp kappa1) (Real.exp_nonneg _)
      hsigmaShifted hwalkCap (C row col).summable_radialMajorant
  calc
    cmp116Lemma1PhysicalCovariancePropagator
          anchor K hc hmass hK C sigma row col =
        ∑' walk : CMP116Lemma1PhysicalCovarianceWalk M Q R,
          cmp116ComplexWeakeningMonomial
              (cmp116Lemma1PhysicalCovarianceWalkActive anchor walk) sigma •
            cmp116Lemma1PhysicalCovarianceWalkEntryTerm
              K hc hmass hK row col walk := by
      rfl
    _ = ∑' length : ℕ,
        ∑' index : CMP99SourcePi4FineWalkIndex M Q R length,
          cmp116ComplexWeakeningMonomial
              (cmp99SourcePi4FineWalkIndex.active anchor index) sigma •
            cmp116PhysicalEndomorphismComplexMatrix
              (cmp99SourcePi4FineWalkIndex.operator
                K hc hmass hK index) row col := hflat.tsum_sigma
    _ = ∑' length : ℕ,
        ∑ index : CMP99SourcePi4FineWalkIndex M Q R length,
          cmp99SourcePi4ComplexFineWalkTerm
            anchor K hc hmass hK sigma index row col := by
      apply tsum_congr
      intro length
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro index _hindex
      rfl
    _ = ∑' length : ℕ,
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma length row col := by
      apply tsum_congr
      intro length
      simpa only [Matrix.sum_apply] using
        congrArg (fun A => A row col)
          (cmp116SourcePi4FullComplexWeakenedCovarianceLayer_eq_sum_fineWalkTerms
            anchor K hc hmass hK sigma length).symm
    _ = cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma row col := by
      rfl

end

end YangMills.RG
