/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixCorePartition
import YangMills.RG.PhysicalWeightedRowKernel

/-!
# Core partitions in the physical weighted-row norm

A source-supported family indexed by a physical core partition can be summed
without paying for the total number of charts.  For each fixed source bond,
all summands except the unique owner core vanish before the target row is
summed.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Passing from a selected finite family to its subtype turns a physical
core partition into a partition indexed by the full subtype. -/
theorem CMP99PhysicalCorePartition.subtype_univ
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    {charts : Finset ι}
    {core : ι → Finset (PhysicalBond d N)}
    (hpartition : CMP99PhysicalCorePartition charts core) :
    CMP99PhysicalCorePartition
      (Finset.univ : Finset ↥charts)
      (fun i : ↥charts => core i.1) := by
  intro source
  obtain ⟨i, hi, hsource, huniq⟩ := hpartition source
  refine ⟨⟨i, hi⟩, Finset.mem_univ _, hsource, ?_⟩
  intro j _ hj
  apply Subtype.ext
  exact huniq j.1 j.2 hj

/-- A source-supported core partition preserves a common weighted-row
amplitude exactly; in particular, no factor `charts.card` appears. -/
theorem physicalCovarianceWeightedRowKernelBound_sum_of_corePartition
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (core : ι → Finset (PhysicalBond d N))
    (term : ι → PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 ≤ rate)
    (hpartition : CMP99PhysicalCorePartition charts core)
    (hsupport : ∀ i, i ∈ charts → ∀ source (v : SUNLieCoord Nc),
      source ∉ core i →
        term i (singlePhysicalBondCochain source v) = 0)
    (hterm : ∀ i, i ∈ charts →
      PhysicalCovarianceWeightedRowKernelBound (term i) dist A rate) :
    PhysicalCovarianceWeightedRowKernelBound
      (∑ i ∈ charts, term i) dist A rate := by
  refine ⟨hA, hrate, ?_⟩
  intro source v
  obtain ⟨i, hi, hsource, huniq⟩ := hpartition source
  have hcolumn :
      (∑ j ∈ charts, term j)
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v) =
        term i (singlePhysicalBondCochain source v) := by
    apply PiLp.ext
    intro target
    simp only [ContinuousLinearMap.sum_apply]
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · intro j hj hji
      have hnot : source ∉ core j := by
        intro hjsource
        exact hji (huniq j hj hjsource)
      rw [hsupport j hj source v hnot]
      rfl
    · intro hni
      exact (hni hi).elim
  rw [hcolumn]
  exact (hterm i hi).2.2 source v

end

end YangMills.RG
