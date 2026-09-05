/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixWalkExpansion
import YangMills.RG.PhysicalWeightedRowKernel

/-!
# Fixed-rate decay of the concrete patched-parametrix walk

This file applies the weighted-row kernel algebra to the already constructed
physical chart head and continuation operators.  It gives an arbitrary-length
ordered product the source-shaped bound

`A_weight * rho_weight^n * exp (-mu * distance)`.

The two weighted amplitudes are explicit row-sum renormalizations of the
existing physical pointwise bounds.  They are intentionally not identified
with the smaller operator-norm ratio used by the separate summability theorem.

Honest scope: this is the fixed-rate ordered-product kernel estimate *toward*
CMP99 `(3.108)` for the concrete patched-parametrix factor species.  It does
not claim that the source's non-exhaustive list of all Sect. C factors has
already been reconstructed.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Weighted amplitude of one physical chart head. -/
noncomputable def cmp99PhysicalPatchHeadWeightedAmplitude
    (c mass Ssum Shead : ℝ) : ℝ :=
  ((2 / min c mass) * Ssum) * Shead

/-- Weighted amplitude of one physical chart continuation. -/
noncomputable def cmp99PhysicalPatchContinuationWeightedAmplitude
    (M κ : ℝ) (R : ℕ) (c mass Ssum Scontinuation : ℝ) : ℝ :=
  cmp99SingleDefectDecayAmplitude M κ R c mass Ssum * Scontinuation

/-- The concrete localized-covariance head has pointwise exponential decay.
The single intermediate bond sum costs one copy of `Ssum`. -/
theorem cmp99PhysicalPatchHead_exponentialKernelBound
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    {R NR : ℕ} {M c mass κ σ Ssum : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (hσκ : σ < κ) (hSsum : 0 ≤ Ssum)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ Ssum)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (htilt :
      (M + |mass|) *
          (Real.exp (κ * (R : ℝ)) - 1) * (NR : ℝ) ≤
        min c mass / 2)
    (i : ↥charts) :
    PhysicalCovarianceExponentialKernelBound
      (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK i)
      dist ((2 / min c mass) * Ssum) (κ - σ) := by
  have hκ : 0 < κ := lt_of_le_of_lt hσ hσκ
  have hC : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK)
      dist (2 / min c mass) κ :=
    cmp99LocalizedPhysicalCovariance_exponentialKernelBound
      dist hsymm (fun p q s => htri p s q) hself
      K (enlarged i) hc hmass hM hNR hrange hbound hK hκ htilt
  have hP : PhysicalCovarianceExponentialKernelBound
      (physicalBondProjection (core i) : PhysicalEndomorphism d N Nc)
      dist 1 κ :=
    physicalBondProjection_exponentialKernelBound dist hself (core i) hκ
  simpa [cmp99PhysicalPatchHead] using
    (physicalCovarianceExponentialKernelBound_comp
      dist htri hσ hσκ hSsum
      (cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK)
      (physicalBondProjection (core i)) hC hP hsum)

/-- The signed concrete chart continuation inherits the already proved defect
kernel estimate; the sign costs nothing. -/
theorem cmp99PhysicalPatchContinuation_exponentialKernelBound
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    {R NR : ℕ} {M c mass κ σ Ssum : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ) (hSsum : 0 ≤ Ssum)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ Ssum)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (htilt :
      (M + |mass|) *
          (Real.exp (κ * (R : ℝ)) - 1) * (NR : ℝ) ≤
        min c mass / 2)
    (i : ↥charts) :
    PhysicalCovarianceExponentialKernelBound
      (cmp99PhysicalPatchContinuation
        charts K enlarged core hc hmass hK i)
      dist (cmp99SingleDefectDecayAmplitude M κ R c mass Ssum)
      (((κ - σ) - σ) - σ) := by
  have hD := cmp99SinglePhysicalParametrixDefect_exponentialKernelBound
    K (hsub i i.property) dist hsymm hself htri
    hM hc hmass hσ h3σκ hSsum hsum hrange hbound hK hNR htilt
  refine ⟨hD.1, hD.2.1, ?_⟩
  intro source target v
  simpa only [cmp99PhysicalPatchContinuation,
    ContinuousLinearMap.neg_apply, PiLp.neg_apply, norm_neg] using
    hD.2.2 source target v

/-- Weighted-row producer for one concrete chart head. -/
theorem cmp99PhysicalPatchHead_weightedRowKernelBound
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι) (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p) (hself : ∀ p, dist p p = 0)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    {R NR : ℕ} {M c mass κ σ Ssum weight Shead : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (hσκ : σ < κ) (hSsum : 0 ≤ Ssum)
    (hweight : 0 ≤ weight) (hShead : 0 ≤ Shead)
    (hsum : ∀ x, ∑ z : PhysicalBond d N,
      Real.exp (-(σ * (dist x z : ℝ))) ≤ Ssum)
    (hsumHead : ∀ source, ∑ target : PhysicalBond d N,
      Real.exp (-(((κ - σ) - weight) *
        (dist target source : ℝ))) ≤ Shead)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (htilt : (M + |mass|) * (Real.exp (κ * (R : ℝ)) - 1) * (NR : ℝ) ≤
      min c mass / 2)
    (i : ↥charts) :
    PhysicalCovarianceWeightedRowKernelBound
      (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK i) dist
      (cmp99PhysicalPatchHeadWeightedAmplitude c mass Ssum Shead) weight := by
  have hExp := cmp99PhysicalPatchHead_exponentialKernelBound
    charts K enlarged core dist hsymm hself htri hM hc hmass hσ hσκ hSsum
    hsum hrange hbound hK hNR htilt i
  simpa [cmp99PhysicalPatchHeadWeightedAmplitude] using
    (physicalCovarianceWeightedRowKernelBound_of_exponential
      _ dist hweight hShead hExp hsumHead)

/-- Weighted-row producer for one concrete signed chart continuation. -/
theorem cmp99PhysicalPatchContinuation_weightedRowKernelBound
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι) (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p) (hself : ∀ p, dist p p = 0)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    {R NR : ℕ}
    {M c mass κ σ Ssum weight Scontinuation : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ) (hSsum : 0 ≤ Ssum)
    (hweight : 0 ≤ weight) (hScontinuation : 0 ≤ Scontinuation)
    (hsum : ∀ x, ∑ z : PhysicalBond d N,
      Real.exp (-(σ * (dist x z : ℝ))) ≤ Ssum)
    (hsumContinuation : ∀ source, ∑ target : PhysicalBond d N,
      Real.exp (-(((((κ - σ) - σ) - σ - weight) *
        (dist target source : ℝ)))) ≤ Scontinuation)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (htilt : (M + |mass|) * (Real.exp (κ * (R : ℝ)) - 1) * (NR : ℝ) ≤
      min c mass / 2)
    (i : ↥charts) :
    PhysicalCovarianceWeightedRowKernelBound
      (cmp99PhysicalPatchContinuation charts K enlarged core hc hmass hK i)
      dist (cmp99PhysicalPatchContinuationWeightedAmplitude
        M κ R c mass Ssum Scontinuation) weight := by
  have hExp := cmp99PhysicalPatchContinuation_exponentialKernelBound
    charts K enlarged core hsub dist hsymm hself htri hM hc hmass hσ h3σκ
    hSsum hsum hrange hbound hK hNR htilt i
  simpa [cmp99PhysicalPatchContinuationWeightedAmplitude] using
    (physicalCovarianceWeightedRowKernelBound_of_exponential
      _ dist hweight hScontinuation hExp hsumContinuation)

theorem cmp99PhysicalWalkTerm_eq_orderedProduct
    {Label ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (walk : CMP99GeneralizedWalk Label ↥charts) :
    walk.term
        (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK) =
      physicalOrderedProduct
        (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK walk.head)
        (walk.tail.map fun step =>
          cmp99PhysicalPatchContinuation
            charts K enlarged core hc hmass hK step.domain) := by
  rw [physicalOrderedProduct_eq_head_mul_prod]
  rfl

/-- Named physical ordered-walk operator.  Keeping the dependent walk term
behind this definition makes the terminal source theorem reproducible without
requiring the elaborator to normalize its entire noncommutative product in the
statement. -/
noncomputable def cmp99PhysicalPatchWalkOperator
    {Label ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (walk : CMP99GeneralizedWalk Label ↥charts) :
    PhysicalEndomorphism d N Nc :=
  walk.term
    (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
    (fun _ => cmp99PhysicalPatchContinuation
      charts K enlarged core hc hmass hK)

/-- The two factorwise weighted estimates for one concrete physical patched
parametrix.  This certificate is constructed below from the physical kernel,
coercivity, finite-range, and row-sum inputs; it is not an assumed whole-walk
bound. -/
structure CMP99PhysicalPatchWeightedCertificate
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι) (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (Ahead rho rate : ℝ) : Prop where
  head : ∀ i : ↥charts,
    PhysicalCovarianceWeightedRowKernelBound
      (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK i)
      dist Ahead rate
  continuation : ∀ i : ↥charts,
    PhysicalCovarianceWeightedRowKernelBound
      (cmp99PhysicalPatchContinuation charts K enlarged core hc hmass hK i)
      dist rho rate

set_option maxHeartbeats 1000000 in
/-- Physical producer of the factorwise certificate.  Both fields are derived
from the concrete chart operators and explicit volume-uniform row sums. -/
noncomputable def cmp99PhysicalPatchWeightedCertificate_of_physicalData
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι) (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p) (hself : ∀ p, dist p p = 0)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    {R NR : ℕ} {M c mass κ σ Ssum weight Shead Scontinuation : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ) (hSsum : 0 ≤ Ssum)
    (hweight : 0 ≤ weight) (hShead : 0 ≤ Shead)
    (hScontinuation : 0 ≤ Scontinuation)
    (hsum : ∀ x, ∑ z : PhysicalBond d N,
      Real.exp (-(σ * (dist x z : ℝ))) ≤ Ssum)
    (hsumHead : ∀ source, ∑ target : PhysicalBond d N,
      Real.exp (-(((κ - σ) - weight) *
        (dist target source : ℝ))) ≤ Shead)
    (hsumContinuation : ∀ source, ∑ target : PhysicalBond d N,
      Real.exp (-(((((κ - σ) - σ) - σ - weight) *
        (dist target source : ℝ)))) ≤ Scontinuation)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (htilt : (M + |mass|) * (Real.exp (κ * (R : ℝ)) - 1) * (NR : ℝ) ≤
      min c mass / 2) :
    CMP99PhysicalPatchWeightedCertificate charts K enlarged core hc hmass hK
      dist (cmp99PhysicalPatchHeadWeightedAmplitude c mass Ssum Shead)
      (cmp99PhysicalPatchContinuationWeightedAmplitude
        M κ R c mass Ssum Scontinuation) weight where
  head i := cmp99PhysicalPatchHead_weightedRowKernelBound
    charts K enlarged core dist hsymm hself htri hM hc hmass hσ
    (by linarith) hSsum hweight hShead hsum hsumHead hrange hbound hK hNR
    htilt i
  continuation i := cmp99PhysicalPatchContinuation_weightedRowKernelBound
    charts K enlarged core hsub dist hsymm hself htri hM hc hmass hσ h3σκ
    hSsum hweight hScontinuation hsum hsumContinuation hrange hbound hK hNR
    htilt i

/-- Concrete fixed-rate, arbitrary-length patched-walk kernel estimate toward
CMP99 `(3.108)`.  The certificate is factorwise; this theorem generates the
whole ordered-product bound `Ahead * rho^n * exp (-rate * distance)`. -/
theorem CMP99PhysicalPatchWeightedCertificate.orderedProduct_exponentialKernelBound_toward_eq3108
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
    (hrate : 0 < rate)
    (head : ↥charts) (tail : List ↥charts) :
    PhysicalCovarianceExponentialKernelBound
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
    (physicalCovarianceExponentialKernelBound_orderedProduct
      (rho := rho) dist htri
      (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK head)
      hrate (Cert.head head)
      (tail.map fun chart =>
        cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK chart) htail)

end

end YangMills.RG
