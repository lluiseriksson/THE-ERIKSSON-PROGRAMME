/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.CoerciveCovariancePositiveSqrt
import YangMills.RG.PhysicalCoerciveCombesThomasInverse
import YangMills.RG.StieltjesKernelIntegration

/-!
# Canonical shifted covariance family

This module packages the actual resolvents `(A + t² I)⁻¹` used in the
Stieltjes representation of the positive covariance root.  It proves their
inverse identities and the coercivity majorant needed for Bochner
integrability.  Identification of the resulting integral with the spectral
positive root is intentionally a separate theorem boundary.
-/

namespace YangMills.RG

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

/-- The canonical shifted covariance family `t ↦ (A + t² I)⁻¹`. -/
noncomputable def shiftedCovarianceFamily
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (t : ℝ) : E →L[ℝ] E :=
  covarianceOfIsCoerciveCLM
    (A + t ^ 2 • ContinuousLinearMap.id ℝ E)
    (by positivity : 0 < c + t ^ 2)
    (isCoerciveCLM_add_smul_id A hA (t ^ 2))

/-- The shifted covariance is a left inverse to `A + t²I`. -/
theorem shiftedCovarianceFamily_comp_precision
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (t : ℝ) :
    (shiftedCovarianceFamily A hc hA t).comp
        (A + t ^ 2 • ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.id ℝ E := by
  exact covarianceOfIsCoerciveCLM_comp_precision _ _ _

/-- The shifted covariance is a right inverse to `A + t²I`. -/
theorem precision_comp_shiftedCovarianceFamily
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (t : ℝ) :
    (A + t ^ 2 • ContinuousLinearMap.id ℝ E).comp
        (shiftedCovarianceFamily A hc hA t) =
      ContinuousLinearMap.id ℝ E := by
  exact precision_comp_covarianceOfIsCoerciveCLM _ _ _

/-- Coercivity gives the scalar Stieltjes majorant uniformly in the
underlying finite-dimensional space. -/
theorem norm_shiftedCovarianceFamily_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (t : ℝ) :
    ‖shiftedCovarianceFamily A hc hA t‖ ≤ (c + t ^ 2)⁻¹ := by
  exact norm_covarianceOfIsCoerciveCLM_le _ (by positivity) _

/-- A coarser shift-independent bound used in the continuity argument. -/
theorem norm_shiftedCovarianceFamily_le_inv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (t : ℝ) :
    ‖shiftedCovarianceFamily A hc hA t‖ ≤ c⁻¹ := by
  exact (norm_shiftedCovarianceFamily_le A hc hA t).trans
    ((inv_le_inv₀ (by positivity : 0 < c + t ^ 2) hc).2
      (by nlinarith [sq_nonneg t]))

/-- Resolvent identity for two scalar shifts.  This is the key continuity
input and uses only the two exact inverse identities above. -/
theorem shiftedCovarianceFamily_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (t u : ℝ) :
    shiftedCovarianceFamily A hc hA t -
        shiftedCovarianceFamily A hc hA u =
      (u ^ 2 - t ^ 2) •
        (shiftedCovarianceFamily A hc hA t).comp
          (shiftedCovarianceFamily A hc hA u) := by
  let Ft := shiftedCovarianceFamily A hc hA t
  let Fu := shiftedCovarianceFamily A hc hA u
  ext x
  have hux : (A + u ^ 2 • ContinuousLinearMap.id ℝ E) (Fu x) = x := by
    exact congrArg (fun L : E →L[ℝ] E => L x)
      (precision_comp_shiftedCovarianceFamily A hc hA u)
  have htx : Ft ((A + t ^ 2 • ContinuousLinearMap.id ℝ E) (Fu x)) = Fu x := by
    exact congrArg (fun L : E →L[ℝ] E => L (Fu x))
      (shiftedCovarianceFamily_comp_precision A hc hA t)
  change Ft x - Fu x = (u ^ 2 - t ^ 2) • Ft (Fu x)
  calc
    Ft x - Fu x =
        Ft ((A + u ^ 2 • ContinuousLinearMap.id ℝ E) (Fu x)) -
          Ft ((A + t ^ 2 • ContinuousLinearMap.id ℝ E) (Fu x)) := by
            rw [hux, htx]
    _ = Ft (((A + u ^ 2 • ContinuousLinearMap.id ℝ E) -
          (A + t ^ 2 • ContinuousLinearMap.id ℝ E)) (Fu x)) := by
            rw [← map_sub]
            rfl
    _ = Ft ((u ^ 2 - t ^ 2) • Fu x) := by
          congr 1
          simp [ContinuousLinearMap.sub_apply,
            ContinuousLinearMap.smul_apply, sub_smul]
    _ = (u ^ 2 - t ^ 2) • Ft (Fu x) := by rw [map_smul]

/-- Quantitative norm form of the resolvent identity. -/
theorem norm_shiftedCovarianceFamily_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (t u : ℝ) :
    ‖shiftedCovarianceFamily A hc hA t -
        shiftedCovarianceFamily A hc hA u‖ ≤
      |u ^ 2 - t ^ 2| * (c⁻¹ * c⁻¹) := by
  rw [shiftedCovarianceFamily_sub A hc hA t u, norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc
    ‖(shiftedCovarianceFamily A hc hA t).comp
        (shiftedCovarianceFamily A hc hA u)‖
        ≤ ‖shiftedCovarianceFamily A hc hA t‖ *
            ‖shiftedCovarianceFamily A hc hA u‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ c⁻¹ * c⁻¹ := by
      exact mul_le_mul
        (norm_shiftedCovarianceFamily_le_inv A hc hA t)
        (norm_shiftedCovarianceFamily_le_inv A hc hA u)
        (norm_nonneg _) (inv_nonneg.mpr hc.le)

/-- The canonical shifted inverse family is continuous in operator norm. -/
theorem continuous_shiftedCovarianceFamily
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) :
    Continuous (shiftedCovarianceFamily A hc hA) := by
  refine continuous_iff_continuousAt.2 fun u =>
    tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun t => norm_nonneg _)
    (fun t => norm_shiftedCovarianceFamily_sub_le A hc hA t u) ?_
  have hcont : ContinuousAt
      (fun t : ℝ => |u ^ 2 - t ^ 2| * (c⁻¹ * c⁻¹)) u :=
    ((continuousAt_const.sub (continuousAt_id.pow 2)).abs).mul
      continuousAt_const
  simpa only [sub_self, abs_zero, zero_mul] using hcont.tendsto

/-- The canonical shifted inverse is Bochner integrable on the positive
half-line.  The proof uses the exact scalar majorant already evaluated in
`StieltjesKernelIntegration`. -/
theorem integrableOn_shiftedCovarianceFamily
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) :
    IntegrableOn (shiftedCovarianceFamily A hc hA) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_Ioi_inv_add_sq hc)
    (continuous_shiftedCovarianceFamily A hc hA).aestronglyMeasurable ?_
  exact ae_of_all _ fun t => norm_shiftedCovarianceFamily_le A hc hA t

/-- The shift-uniform Combes--Thomas estimate integrates for the *canonical*
resolvent family, with no abstract family or integrability hypothesis left to
the caller.  This localizes the Stieltjes integral operator itself; identifying
that operator with the spectral positive covariance root remains separate. -/
theorem physicalShiftedCovarianceFamily_stieltjes_exponentialKernelBound
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (hself : ∀ p, dist p p = 0)
    {θ : ℝ} (hθ : 0 < θ) {R NR : ℕ} {M c : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {K : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hcoer : IsCoerciveCLM K c)
    (hbudget : M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c / 2) :
    PhysicalCovarianceExponentialKernelBound
      (stieltjesIntegralOperator (shiftedCovarianceFamily K hc hcoer))
      dist (2 / Real.sqrt c) θ := by
  apply physicalCovariance_exponentialKernelBound_stieltjesIntegralOperator
    hc hθ dist (shiftedCovarianceFamily K hc hcoer)
    (integrableOn_shiftedCovarianceFamily K hc hcoer)
  intro t _ht
  exact physicalCovariance_exponentialKernelBound_of_coercive_add_smul_id
    dist hsymm htri hself hθ hM hc (sq_nonneg t) hNR hrange hbound hcoer
    (precision_comp_shiftedCovarianceFamily K hc hcoer t) hbudget

end

end YangMills.RG
