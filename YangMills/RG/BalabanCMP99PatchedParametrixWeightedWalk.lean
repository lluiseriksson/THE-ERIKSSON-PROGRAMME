/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixFixedRateWalkDecay

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- A factorwise physical certificate bounds every literal ordered physical
patch product in the fixed-rate weighted-row norm. -/
theorem CMP99PhysicalPatchWeightedCertificate.orderedProduct_weightedRow
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    {charts : Finset ι} {K : PhysicalEndomorphism d N Nc}
    {enlarged core : ι → Finset (PhysicalBond d N)}
    {c mass : ℝ} {hc : 0 < c} {hmass : 0 < mass}
    {hK : IsCoerciveCLM K c}
    {dist : PhysicalBond d N → PhysicalBond d N → ℕ}
    {Ahead rho rate : ℝ}
    (Cert : CMP99PhysicalPatchWeightedCertificate
      charts K enlarged core hc hmass hK dist Ahead rho rate)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    (head : ↥charts) (tail : List ↥charts) :
    PhysicalCovarianceWeightedRowKernelBound
      (physicalOrderedProduct
        (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK head)
        (tail.map fun chart =>
          cmp99PhysicalPatchContinuation
            charts K enlarged core hc hmass hK chart))
      dist (Ahead * rho ^ tail.length) rate := by
  have htail : ∀ next,
      next ∈ (tail.map fun chart =>
        cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK chart) →
      PhysicalCovarianceWeightedRowKernelBound next dist rho rate := by
    intro next hnext
    obtain ⟨chart, _hchart, rfl⟩ := List.mem_map.mp hnext
    exact Cert.continuation chart
  simpa only [List.length_map] using
    (physicalCovarianceWeightedRowKernelBound_orderedProduct
      (rho := rho) dist htri
      (cmp99PhysicalPatchHead
        charts K enlarged core hc hmass hK head)
      (Cert.head head)
      (tail.map fun chart =>
        cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK chart)
      htail)

end

end YangMills.RG
