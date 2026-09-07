/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixNeumann
import YangMills.RG.BalabanCMP99SourceBasePartition
import YangMills.RG.BalabanCMP99SourcePi4RangeProtection
import YangMills.RG.BalabanCMP99SectionCSourcePi4CovarianceDifference

/-!
# Exact source `Pi^4` patched covariance

The complex source-walk estimates used by CMP116 are naturally proved one
anchored head at a time.  One anchored head is not, however, the inverse of
the global precision.  This file constructs the complete source covariance:

* the heads are the literal source cells `Pi`;
* their cores are the exact source-cell bond partition;
* their enlarged regions are the bilateral physical supports of `Pi^4`;
* the complete patched parametrix is corrected by its defect Neumann series.

The terminal theorem derives the defect contraction from physical finite
range, kernel, coercivity, and exponential-row inputs.  Thus the exact
identity `K C = 1` does not receive a renamed inverse hypothesis.

This operator-level result deliberately does not identify a single-head
complex contour matrix with the complete covariance.  That remaining
all-head matrix bridge must preserve the source weakening variables.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Complete source patched covariance with literal `Pi` cores and `Pi^4`
enlargements.  In particular, this is not a single anchored-head term. -/
noncomputable def cmp116SourcePi4ExactPatchedCovariance
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    PhysicalEndomorphism M Q Nc :=
  cmp99CorrectedPatchedPhysicalCovariance
    (Finset.univ : Finset (FinBox 4 Q))
    K
    (cmp99SourcePi4PhysicalBondSupport (M := M))
    (cmp99SourceBaseCellBondCore (M := M))
    hc hmass hK

/-- Once the literal patched defect contracts, the complete source covariance
is an exact right inverse of the physical precision.  The core partition is
generated internally by source-cell ownership. -/
theorem comp_cmp116SourcePi4ExactPatchedCovariance_eq_id_of_contraction
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    K.comp
        (cmp116SourcePi4ExactPatchedCovariance K hc hmass hK) =
      ContinuousLinearMap.id ℝ
        (PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc) := by
  exact
    comp_cmp99CorrectedPatchedPhysicalCovariance_eq_id
      (Finset.univ : Finset (FinBox 4 Q))
      K
      (cmp99SourcePi4PhysicalBondSupport (M := M))
      (cmp99SourceBaseCellBondCore (M := M))
      hc hmass hK
      cmp99SourceBaseCellBondCore_corePartition
      hD

/-- Source-physical producer of the exact inverse identity.

The visible scalar condition is the row-sum contraction of the complete
patched defect.  The zero separation used here is always valid and is enough
for exactness; a future positive source collar separation can sharpen the
amplitude without changing this theorem's architecture. -/
theorem comp_cmp116SourcePi4ExactPatchedCovariance_eq_id
    {M Q Nc R NR : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hsymm : ∀ p q : PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist p q = physicalBondDist q p)
    (hself : ∀ p : PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist p p = 0)
    (htri : ∀ x y z : PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist x y ≤
        physicalBondDist x z + physicalBondDist z y)
    {Cker c mass κ σ Ssum Sdef : ℝ}
    (hCker : 0 ≤ Cker) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ)
    (hSsum : 0 ≤ Ssum) (hSdef : 0 ≤ Sdef)
    (hsum : ∀ x : PhysicalBond 4 (M * (2 * Q)),
      ∑ z : PhysicalBond 4 (M * (2 * Q)),
        Real.exp (-(σ * (physicalBondDist x z : ℝ))) ≤ Ssum)
    (hsumDef : ∀ x : PhysicalBond 4 (M * (2 * Q)),
      ∑ z : PhysicalBond 4 (M * (2 * Q)),
        Real.exp (-(((((κ - σ) - σ) - σ) / 2) *
          (physicalBondDist x z : ℝ))) ≤ Sdef)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => Cker))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond 4 (M * (2 * Q)),
      (Finset.univ.filter
        (fun y => physicalBondDist x y ≤ R)).card ≤ NR)
    (htilt :
      (Cker + |mass|) *
          (Real.exp (κ * (R : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (hsmall :
      cmp99SingleDefectDecayAmplitude Cker κ R c mass Ssum *
          Sdef < 1) :
    K.comp
        (cmp116SourcePi4ExactPatchedCovariance K hc hmass hK) =
      ContinuousLinearMap.id ℝ
        (PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc) := by
  have hsub : ∀ cell : FinBox 4 Q,
      cell ∈ (Finset.univ : Finset (FinBox 4 Q)) →
      cmp99SourceBaseCellBondCore (M := M) cell ⊆
        cmp99SourcePi4PhysicalBondSupport cell := by
    intro cell _hcell
    exact cmp99SourceBaseCellBondCore_subset_pi4PhysicalSupport
      (M := M) (Q := Q) cell hsourceRange
  have hsep : ∀ cell : FinBox 4 Q,
      cell ∈ (Finset.univ : Finset (FinBox 4 Q)) →
      CMP99CoreExteriorSeparated
        (cmp99SourceBaseCellBondCore (M := M) cell)
        (cmp99SourcePi4PhysicalBondSupport cell)
        physicalBondDist 0 := by
    intro cell _hcell source _hsource target _htarget
    exact Nat.zero_le _
  have hDkernel :
      PhysicalCovarianceExponentialKernelBound
        (cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)
        physicalBondDist
        (cmp99SingleDefectDecayAmplitude Cker κ R c mass Ssum)
        ((((κ - σ) - σ) - σ) / 2) := by
    simpa using
      (cmp99PatchedPhysicalParametrixDefect_exponentialKernelBound
        (Finset.univ : Finset (FinBox 4 Q))
        K
        (cmp99SourcePi4PhysicalBondSupport (M := M))
        (cmp99SourceBaseCellBondCore (M := M))
        cmp99SourceBaseCellBondCore_corePartition
        hsub physicalBondDist hsymm hself htri
        hCker hc hmass hσ h3σκ hSsum hsum
        hrange hbound hK hNR htilt hsep)
  have hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1 := by
    exact
      cmp99PatchedPhysicalParametrixDefect_norm_lt_one_of_exponential
        (Finset.univ : Finset (FinBox 4 Q))
        K
        (cmp99SourcePi4PhysicalBondSupport (M := M))
        (cmp99SourceBaseCellBondCore (M := M))
        hc hmass hK physicalBondDist hsymm
        hSdef hDkernel hsumDef hsmall
  exact comp_cmp116SourcePi4ExactPatchedCovariance_eq_id_of_contraction
    K hc hmass hK hD

end

end YangMills.RG
