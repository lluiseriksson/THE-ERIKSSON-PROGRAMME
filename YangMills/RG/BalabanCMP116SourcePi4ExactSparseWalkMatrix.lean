/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixSparseWalk
import YangMills.RG.BalabanCMP116PhysicalEndomorphismMatrix

/-!
# Exact all-head source `Pi^4` sparse-walk matrix

The source contour estimates are naturally organized one anchored head at a
time.  The inverse of the physical precision is not one such anchored series:
it contains every source-cell head.  This file records the exact all-head
object, still ordered by walk length as in the defect Neumann series.

The terminal theorem says that the physical precision matrix times the matrix
of the complete sparse-walk series is the identity.  No single-head series is
identified with the covariance, and no matrix inverse hypothesis is supplied.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The exact length-`n` layer: sum over every literal source-cell head and
every physically admissible continuation word. -/
noncomputable def cmp116SourcePi4ExactSparseWalkLayer
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (R n : ℕ) :
    PhysicalEndomorphism M Q Nc :=
  ∑ head : ↥(Finset.univ : Finset (FinBox 4 Q)),
    ∑ word ∈ cmp99PhysicalPatchAdmissibleWords
        (Finset.univ : Finset (FinBox 4 Q))
        (cmp99SourceBaseCellBondCore (M := M))
        (cmp99SourcePi4PhysicalBondSupport (M := M))
        physicalBondDist R n,
      (cmp99SingleSpeciesWalk head word).term
        (cmp99PhysicalPatchHead
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)

/-- The complete corrected covariance is literally the length-ordered sum of
all source heads and all physically surviving continuation words. -/
theorem cmp116SourcePi4ExactPatchedCovariance_eq_tsum_sparseWalkLayers
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116SourcePi4ExactPatchedCovariance K hc hmass hK =
      ∑' n : ℕ,
        cmp116SourcePi4ExactSparseWalkLayer K hc hmass hK R n := by
  have hsub : ∀ cell : FinBox 4 Q,
      cell ∈ (Finset.univ : Finset (FinBox 4 Q)) →
      cmp99SourceBaseCellBondCore (M := M) cell ⊆
        cmp99SourcePi4PhysicalBondSupport cell := by
    intro cell _hcell
    exact cmp99SourceBaseCellBondCore_subset_pi4PhysicalSupport
      (M := M) (Q := Q) cell hsourceRange
  simpa [cmp116SourcePi4ExactPatchedCovariance,
    cmp116SourcePi4ExactSparseWalkLayer] using
    (cmp99CorrectedPatchedPhysicalCovariance_eq_tsum_sparse_walk_layers
      (Finset.univ : Finset (FinBox 4 Q))
      K
      (cmp99SourcePi4PhysicalBondSupport (M := M))
      (cmp99SourceBaseCellBondCore (M := M))
      hsub physicalBondDist
      hrange hc hmass hK hD)

/-- Matrix form of the complete all-head sparse-walk inverse.  The matrix
contains the length-ordered physical series, rather than a fixed-head
contour contribution. -/
theorem cmp116SourcePi4_precision_mul_tsum_sparseWalkLayerMatrix_eq_one
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116PhysicalEndomorphismComplexMatrix K *
        cmp116PhysicalEndomorphismComplexMatrix
          (∑' n : ℕ,
            cmp116SourcePi4ExactSparseWalkLayer
              K hc hmass hK R n) =
      1 := by
  rw [← cmp116SourcePi4ExactPatchedCovariance_eq_tsum_sparseWalkLayers
    K hsourceRange hrange hc hmass hK hD]
  exact cmp116SourcePi4_precision_mul_exactCovarianceMatrix_eq_one
    K hc hmass hK hD

end

end YangMills.RG
