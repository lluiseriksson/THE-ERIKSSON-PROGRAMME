/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixFixedRateWalkDecay

/-!
# Volume-uniform weighted decay for the physical CMP99 patched parametrix

The fixed-rate walk theorem requires three exponential row sums: the loss
used in the physical parametrix construction, the remaining rate of the head,
and the remaining rate of a continuation.  This file generates all three
from the physical bond metric and the already-proved geometric shell count.

The resulting certificate contains no abstract row-sum constants.  Its three
scalar hypotheses are deliberately visible: each residual exponential rate
must dominate the coarse shell branching `2^d`.  The weighted continuation
ratio produced here is not identified with the separate operator-norm ratio
used by the unweighted summability theorem.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Explicit, volume-uniform exponential row-sum constant for the physical
bond metric. -/
def cmp99PhysicalBondGeometricRowSum (d : ℕ) (rate : ℝ) : ℝ :=
  (((2 ^ d) * d : ℕ) : ℝ) *
    (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-rate))⁻¹

/-- Positivity of the geometric row-sum constant under its exact scalar
convergence condition. -/
theorem cmp99PhysicalBondGeometricRowSum_nonneg
    {d : ℕ} {rate : ℝ}
    (hgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-rate) < 1) :
    0 ≤ cmp99PhysicalBondGeometricRowSum d rate := by
  have hden :
      0 < 1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-rate) :=
    sub_pos.mpr hgeom
  exact mul_nonneg (by positivity) (inv_nonneg.mpr hden.le)

/-- The physical exponential sum is bounded by the explicit geometric
constant, independently of the torus volume. -/
theorem physicalBondDist_exp_sum_le_cmp99GeometricRowSum
    {d N : ℕ} [NeZero N]
    (source : PhysicalBond d N) {rate : ℝ}
    (hgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-rate) < 1) :
    ∑ target : PhysicalBond d N,
        Real.exp (-(rate * (physicalBondDist target source : ℝ))) ≤
      cmp99PhysicalBondGeometricRowSum d rate := by
  rw [show (∑ target : PhysicalBond d N,
      Real.exp (-(rate * (physicalBondDist target source : ℝ)))) =
      ∑ target : PhysicalBond d N,
        Real.exp (-(rate * (physicalBondDist source target : ℝ))) by
    apply Finset.sum_congr rfl
    intro target _
    rw [physicalBondDist_comm]]
  simpa [cmp99PhysicalBondGeometricRowSum] using
    physicalBondDist_exp_sum_le_geometric
      (d := d) (N := N) source hgeom

set_option maxHeartbeats 2000000 in
/-- Fully geometric producer of the fixed-rate physical patch certificate.

The three abstract constants and their pointwise row-sum hypotheses from
`cmp99PhysicalPatchWeightedCertificate_of_physicalData` are generated here
at the rates `sigma`, `kappa - sigma - mu`, and
`kappa - 3 sigma - mu` respectively. -/
noncomputable def
    cmp99PhysicalPatchWeightedCertificate_of_geometricPhysicalData
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι) (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    {R NR : ℕ} {M c mass κ σ μ : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ) (hμ : 0 ≤ μ)
    (hgeomBase :
      ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ) < 1)
    (hgeomHead :
      ((2 ^ d : ℕ) : ℝ) * Real.exp (-((κ - σ) - μ)) < 1)
    (hgeomContinuation :
      ((2 ^ d : ℕ) : ℝ) *
        Real.exp (-((((κ - σ) - σ) - σ) - μ)) < 1)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter
        (fun y => physicalBondDist x y ≤ R)).card ≤ NR)
    (htilt :
      (M + |mass|) *
          (Real.exp (κ * (R : ℝ)) - 1) * (NR : ℝ) ≤
        min c mass / 2) :
    CMP99PhysicalPatchWeightedCertificate charts K enlarged core hc hmass hK
      physicalBondDist
      (cmp99PhysicalPatchHeadWeightedAmplitude c mass
        (cmp99PhysicalBondGeometricRowSum d σ)
        (cmp99PhysicalBondGeometricRowSum d ((κ - σ) - μ)))
      (cmp99PhysicalPatchContinuationWeightedAmplitude M κ R c mass
        (cmp99PhysicalBondGeometricRowSum d σ)
        (cmp99PhysicalBondGeometricRowSum d
          ((((κ - σ) - σ) - σ) - μ)))
      μ := by
  apply cmp99PhysicalPatchWeightedCertificate_of_physicalData
    charts K enlarged core hsub physicalBondDist
    physicalBondDist_comm physicalBondDist_self
    (fun target source middle =>
      physicalBondDist_triangle target middle source)
    hM hc hmass hσ h3σκ
    (cmp99PhysicalBondGeometricRowSum_nonneg hgeomBase)
    hμ
    (cmp99PhysicalBondGeometricRowSum_nonneg hgeomHead)
    (cmp99PhysicalBondGeometricRowSum_nonneg hgeomContinuation)
    (fun source => by
      simpa only [physicalBondDist_comm] using
        physicalBondDist_exp_sum_le_cmp99GeometricRowSum source hgeomBase)
    (fun source =>
      physicalBondDist_exp_sum_le_cmp99GeometricRowSum source hgeomHead)
    (fun source =>
      physicalBondDist_exp_sum_le_cmp99GeometricRowSum
        source hgeomContinuation)
    hrange hbound hK hNR htilt

/-- Fixed-rate arbitrary-length decay with every exponential row sum replaced
by an explicit volume-uniform physical constant. -/
theorem cmp99PhysicalPatchOrderedProduct_exponentialKernelBound_geometric
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    {charts : Finset ι} {K : PhysicalEndomorphism d N Nc}
    {enlarged core : ι → Finset (PhysicalBond d N)}
    {c mass κ σ μ : ℝ} {R : ℕ}
    {hc : 0 < c} {hmass : 0 < mass} {hK : IsCoerciveCLM K c}
    (Cert : CMP99PhysicalPatchWeightedCertificate charts K enlarged core
      hc hmass hK physicalBondDist
      (cmp99PhysicalPatchHeadWeightedAmplitude c mass
        (cmp99PhysicalBondGeometricRowSum d σ)
        (cmp99PhysicalBondGeometricRowSum d ((κ - σ) - μ)))
      (cmp99PhysicalPatchContinuationWeightedAmplitude M κ R c mass
        (cmp99PhysicalBondGeometricRowSum d σ)
        (cmp99PhysicalBondGeometricRowSum d
          ((((κ - σ) - σ) - σ) - μ)))
      μ)
    (hμ : 0 < μ) (head : ↥charts) (tail : List ↥charts) :
    PhysicalCovarianceExponentialKernelBound
      (physicalOrderedProduct
        (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK head)
        (tail.map fun chart =>
          cmp99PhysicalPatchContinuation
            charts K enlarged core hc hmass hK chart))
      physicalBondDist
      (cmp99PhysicalPatchHeadWeightedAmplitude c mass
        (cmp99PhysicalBondGeometricRowSum d σ)
        (cmp99PhysicalBondGeometricRowSum d ((κ - σ) - μ)) *
        cmp99PhysicalPatchContinuationWeightedAmplitude M κ R c mass
          (cmp99PhysicalBondGeometricRowSum d σ)
          (cmp99PhysicalBondGeometricRowSum d
            ((((κ - σ) - σ) - σ) - μ)) ^ tail.length)
      μ := by
  exact Cert.orderedProduct_exponentialKernelBound_toward_eq3108
    (fun target source middle =>
      physicalBondDist_triangle target middle source)
    hμ head tail

end

end YangMills.RG
