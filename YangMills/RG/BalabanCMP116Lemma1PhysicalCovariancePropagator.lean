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
The literal source-Pi4 covariance is stored instead as a length `tsum` whose
fibres are finite dependent types of physical walks.  This module supplies
the exact dependent reindexing

`Sigma length, CMP99SourcePi4FineWalkIndex M Q R length`

and proves that the internally constructed L1 propagator is the literal
complex covariance `cmp116SourcePi4FullComplexWeakenedCovarianceMatrix`.
The exchange of the sigma sum with the length/fibre sums uses the radial
summability already carried by the L1 certificate; no conditionally
convergent rearrangement is made.

Honest scope: this is the physical `G(s)` bridge only.  The current literal
`H(s)` expansion multiplies several sigma-dependent fine-walk factors, so it
does not factor through the square-free active `Finset` used here without an
additional multiplicity-aware expansion.  No `H0(s)` producer is supplied.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

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

/-- The generic L1 propagator specialized to the dependent physical walk
index is exactly the literal source-Pi4 complex covariance `G(s)`.

Besides the L1 source certificate, the hypotheses are precisely those used
by the existing physical theorem which promotes the pointwise length series
to a matrix `tsum`. -/
theorem cmp116Lemma1PhysicalCovariancePropagator_eq
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate radius Rweak : ℝ}
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    {treeLength : CMP116Lemma1PhysicalCovarianceWalk M Q R → ℕ}
    {baseWeight : CMP116Lemma1PhysicalCovarianceWalk M Q R → ℝ}
    {B0 delta0 delta1 kappa1 : ℝ}
    (C : CMP116Lemma1WeakenedPropagatorCertificate
      (cmp116Lemma1PhysicalCovarianceWalkActive anchor)
      (cmp116Lemma1PhysicalCovarianceWalkTerm K hc hmass hK)
      treeLength baseWeight B0 delta0 delta1 (M : ℝ) kappa1)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1) :
    C.propagator sigma =
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma := by
  let shiftedRadius : FinBox 4 (2 * Q) → ℝ :=
    fun _ => Real.exp kappa1 - 1
  have hR : 1 ≤ Real.exp kappa1 :=
    Real.one_le_exp C.kappa1_nonneg
  have hsigmaShifted :
      sigma ∈ cmp116ComplexShiftedWeakeningPolydisc shiftedRadius := by
    intro d
    simpa [shiftedRadius] using hsigma d
  have hwalkCap : ∀ walk d,
      d ∈ cmp116Lemma1PhysicalCovarianceWalkActive anchor walk →
        1 + shiftedRadius d ≤ Real.exp kappa1 := by
    intro walk d _hd
    simp [shiftedRadius]
  have hflat : Summable fun walk :
      CMP116Lemma1PhysicalCovarianceWalk M Q R =>
        cmp116ComplexWeakeningMonomial
            (cmp116Lemma1PhysicalCovarianceWalkActive anchor walk) sigma •
          cmp116Lemma1PhysicalCovarianceWalkTerm K hc hmass hK walk :=
    summable_cmp116ComplexWeakenedRandomWalkSeries
      (cmp116Lemma1PhysicalCovarianceWalkActive anchor)
      (cmp116Lemma1PhysicalCovarianceWalkTerm K hc hmass hK)
      sigma shiftedRadius (Real.exp kappa1) (Real.exp_nonneg _)
      hsigmaShifted hwalkCap C.summable_radialMajorant
  have hmatrix :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_eq_tsum_layers_of_source
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri
      hsourceRange hΔ hΔ1 sigma hradius hRweak hdiff hcap hsmall
  calc
    C.propagator sigma =
        ∑' walk : CMP116Lemma1PhysicalCovarianceWalk M Q R,
          cmp116ComplexWeakeningMonomial
              (cmp116Lemma1PhysicalCovarianceWalkActive anchor walk) sigma •
            cmp116Lemma1PhysicalCovarianceWalkTerm K hc hmass hK walk := by
      rfl
    _ = ∑' length : ℕ,
        ∑' index : CMP99SourcePi4FineWalkIndex M Q R length,
          cmp116ComplexWeakeningMonomial
              (cmp99SourcePi4FineWalkIndex.active anchor index) sigma •
            cmp116PhysicalEndomorphismComplexMatrix
              (cmp99SourcePi4FineWalkIndex.operator
                K hc hmass hK index) := hflat.tsum_sigma
    _ = ∑' length : ℕ,
        ∑ index : CMP99SourcePi4FineWalkIndex M Q R length,
          cmp99SourcePi4ComplexFineWalkTerm
            anchor K hc hmass hK sigma index := by
      apply tsum_congr
      intro length
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro index _hindex
      rfl
    _ = ∑' length : ℕ,
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma length := by
      apply tsum_congr
      intro length
      exact
        (cmp116SourcePi4FullComplexWeakenedCovarianceLayer_eq_sum_fineWalkTerms
          anchor K hc hmass hK sigma length).symm
    _ = cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma := hmatrix.symm

end

end YangMills.RG
