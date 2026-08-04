/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.CoerciveCovariancePositiveSqrt
import YangMills.RG.PhysicalCoerciveCombesThomasInverse
import YangMills.RG.StieltjesKernelIntegration
import YangMills.RG.PhysicalGaugeCovariancePositiveRoot
import Mathlib.MeasureTheory.Function.L2Space

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

/-- Every nonzero eigenvector of a strictly coercive operator has a positive
eigenvalue. -/
theorem eigenvalue_pos_of_isCoerciveCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) {x : E} {lam : ℝ}
    (hx0 : x ≠ 0) (hx : A x = lam • x) : 0 < lam := by
  by_contra hn
  have hlam_nonpos : lam ≤ 0 := le_of_not_gt hn
  have hcoer := hA x
  rw [hx, real_inner_smul_right, real_inner_self_eq_norm_sq] at hcoer
  have hxnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  nlinarith

/-- On an eigenvector of the precision, the canonical shifted covariance is
the corresponding scalar shifted inverse. -/
theorem shiftedCovarianceFamily_apply_of_eigenvector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) {x : E} {lam : ℝ}
    (hx0 : x ≠ 0) (hx : A x = lam • x) (t : ℝ) :
    shiftedCovarianceFamily A hc hA t x = (lam + t ^ 2)⁻¹ • x := by
  have hlam : 0 < lam := eigenvalue_pos_of_isCoerciveCLM A hc hA hx0 hx
  have hden : lam + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  calc
    shiftedCovarianceFamily A hc hA t x =
        shiftedCovarianceFamily A hc hA t
          ((A + t ^ 2 • ContinuousLinearMap.id ℝ E)
            ((lam + t ^ 2)⁻¹ • x)) := by
      congr 1
      simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        hx, ← add_smul, hden]
    _ = (lam + t ^ 2)⁻¹ • x := by
      exact congrArg (fun L : E →L[ℝ] E => L ((lam + t ^ 2)⁻¹ • x))
        (shiftedCovarianceFamily_comp_precision A hc hA t)

/-- The normalized canonical Stieltjes integral acts by `lam⁻¹ᐟ²` on every
precision eigenvector of eigenvalue `lam`. -/
theorem stieltjesIntegralOperator_shifted_apply_of_eigenvector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) {x : E} {lam : ℝ}
    (hx0 : x ≠ 0) (hx : A x = lam • x) :
    stieltjesIntegralOperator (shiftedCovarianceFamily A hc hA) x =
      (Real.sqrt lam)⁻¹ • x := by
  have hlam : 0 < lam := eigenvalue_pos_of_isCoerciveCLM A hc hA hx0 hx
  have hFint := integrableOn_shiftedCovarianceFamily A hc hA
  unfold stieltjesIntegralOperator
  rw [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.integral_apply hFint x]
  simp_rw [shiftedCovarianceFamily_apply_of_eigenvector A hc hA hx0 hx]
  rw [integral_smul_const, integral_Ioi_inv_add_sq hlam, smul_smul]
  congr 1
  field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hlam).ne']

/-- Every shifted covariance is positive when the precision is symmetric. -/
theorem shiftedCovarianceFamily_isPositive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) (t : ℝ) :
    (shiftedCovarianceFamily A hc hA t).IsPositive := by
  apply covarianceOfIsCoerciveCLM_isPositive
  intro x y
  change inner ℝ (A x + t ^ 2 • x) y = inner ℝ x (A y + t ^ 2 • y)
  calc
    inner ℝ (A x + t ^ 2 • x) y =
        inner ℝ (A x) y + t ^ 2 * inner ℝ x y := by
      rw [inner_add_left, real_inner_smul_left]
    _ = inner ℝ x (A y) + t ^ 2 * inner ℝ x y := by
      have hs : inner ℝ (A x) y = inner ℝ x (A y) := hSymm x y
      exact congrArg (fun z : ℝ => z + t ^ 2 * inner ℝ x y) hs
    _ = inner ℝ x (A y + t ^ 2 • y) := by
      rw [inner_add_right, real_inner_smul_right]

/-- The normalized canonical Stieltjes integral is itself a positive
continuous endomorphism. -/
theorem stieltjesIntegralOperator_shifted_isPositive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) :
    (stieltjesIntegralOperator
      (shiftedCovarianceFamily A hc hA)).IsPositive := by
  let F := shiftedCovarianceFamily A hc hA
  let J := stieltjesIntegralOperator F
  have hFint : IntegrableOn F (Ioi 0) :=
    integrableOn_shiftedCovarianceFamily A hc hA
  have hFpos : ∀ t, (F t).IsPositive :=
    fun t => shiftedCovarianceFamily_isPositive A hc hA hSymm t
  have hJinner (x y : E) :
      inner ℝ x (J y) =
        (2 / Real.pi) * ∫ t : ℝ in Ioi 0, inner ℝ x (F t y) := by
    have hFyint : IntegrableOn (fun t => F t y) (Ioi 0) :=
      (ContinuousLinearMap.apply ℝ E y).integrable_comp hFint
    unfold J stieltjesIntegralOperator
    rw [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.integral_apply hFint y,
      real_inner_smul_right, ← integral_inner hFyint x]
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨?_, ?_⟩
  · intro x y
    change inner ℝ (J x) y = inner ℝ x (J y)
    calc
      inner ℝ (J x) y = inner ℝ y (J x) := real_inner_comm _ _
      _ = (2 / Real.pi) * ∫ t : ℝ in Ioi 0, inner ℝ y (F t x) :=
        hJinner y x
      _ = (2 / Real.pi) * ∫ t : ℝ in Ioi 0, inner ℝ x (F t y) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with t
        simpa [real_inner_comm] using (hFpos t).isSymmetric x y
      _ = inner ℝ x (J y) := (hJinner x y).symm
  · intro x
    change 0 ≤ inner ℝ (J x) x
    calc
      0 ≤ (2 / Real.pi) * ∫ t : ℝ in Ioi 0, inner ℝ x (F t x) :=
        mul_nonneg (by positivity)
          (integral_nonneg fun t => (hFpos t).inner_nonneg_right x)
      _ = inner ℝ x (J x) := (hJinner x x).symm
      _ = inner ℝ (J x) x := real_inner_comm _ _

/-- The unshifted covariance acts by `lam⁻¹` on a precision eigenvector. -/
theorem covarianceOfIsCoerciveCLM_apply_of_eigenvector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) {x : E} {lam : ℝ}
    (hx0 : x ≠ 0) (hx : A x = lam • x) :
    covarianceOfIsCoerciveCLM A hc hA x = lam⁻¹ • x := by
  have hlam : 0 < lam := eigenvalue_pos_of_isCoerciveCLM A hc hA hx0 hx
  calc
    covarianceOfIsCoerciveCLM A hc hA x =
        covarianceOfIsCoerciveCLM A hc hA (A (lam⁻¹ • x)) := by
      congr 1
      rw [map_smul, hx, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    _ = lam⁻¹ • x := covarianceOfIsCoerciveCLM_apply_precision _ _ _ _

/-- The normalized canonical Stieltjes integral squares exactly to the
canonical covariance. -/
theorem stieltjesIntegralOperator_shifted_comp_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) :
    (stieltjesIntegralOperator (shiftedCovarianceFamily A hc hA)).comp
        (stieltjesIntegralOperator (shiftedCovarianceFamily A hc hA)) =
      covarianceOfIsCoerciveCLM A hc hA := by
  let hAlin : A.toLinearMap.IsSymmetric := hSymm
  let b := hAlin.eigenvectorBasis rfl
  let J := stieltjesIntegralOperator (shiftedCovarianceFamily A hc hA)
  have hlin : (J.comp J).toLinearMap =
      (covarianceOfIsCoerciveCLM A hc hA).toLinearMap := by
    apply b.toBasis.ext
    intro i
    have hbi0 : b i ≠ 0 := by
      intro hzero
      have hnorm := b.norm_eq_one i
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    have heig : A (b i) = hAlin.eigenvalues rfl i • b i :=
      hAlin.apply_eigenvectorBasis rfl i
    have hlam : 0 < hAlin.eigenvalues rfl i :=
      eigenvalue_pos_of_isCoerciveCLM A hc hA hbi0 heig
    have hJ : J (b i) = (Real.sqrt (hAlin.eigenvalues rfl i))⁻¹ • b i :=
      stieltjesIntegralOperator_shifted_apply_of_eigenvector
        A hc hA hbi0 heig
    have hC : covarianceOfIsCoerciveCLM A hc hA (b i) =
        (hAlin.eigenvalues rfl i)⁻¹ • b i :=
      covarianceOfIsCoerciveCLM_apply_of_eigenvector A hc hA hbi0 heig
    change J (J (b i)) = covarianceOfIsCoerciveCLM A hc hA (b i)
    rw [hJ, map_smul, hJ, smul_smul, hC]
    congr 1
    have hsqrt : Real.sqrt (hAlin.eigenvalues rfl i) ^ 2 =
        hAlin.eigenvalues rfl i := Real.sq_sqrt hlam.le
    field_simp [(Real.sqrt_pos.2 hlam).ne', hlam.ne']
    nlinarith
  exact ContinuousLinearMap.ext fun x => LinearMap.congr_fun hlin x

/-- **Canonical Stieltjes identification.**  For a symmetric coercive
finite-dimensional real precision, the normalized integral of its canonical
shifted inverses is exactly the spectral positive covariance root. -/
theorem stieltjesIntegralOperator_shifted_eq_covarianceSqrt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) :
    stieltjesIntegralOperator (shiftedCovarianceFamily A hc hA) =
      covarianceSqrtOfIsCoerciveCLM A hc hA hSymm := by
  apply eq_of_isPositive_of_comp_self_eq
    (stieltjesIntegralOperator_shifted_isPositive A hc hA hSymm)
    (covarianceSqrtOfIsCoerciveCLM_isPositive A hc hA hSymm)
    (stieltjesIntegralOperator_shifted_comp_self A hc hA hSymm)
    (covarianceSqrtOfIsCoerciveCLM_comp_self A hc hA hSymm)

/-- The shift-uniform Combes--Thomas estimate integrates for the *canonical*
resolvent family, with no abstract family or integrability hypothesis left to
the caller. -/
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

/-- **Localized spectral-root capstone.**  The canonical positive covariance
root itself inherits the integrated shift-uniform Combes--Thomas bound. -/
theorem physicalCovarianceSqrt_exponentialKernelBound_of_shiftUniform
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
    (hcoer : IsCoerciveCLM K c) (hKsymm : K.IsSymmetric)
    (hbudget : M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c / 2) :
    PhysicalCovarianceExponentialKernelBound
      (covarianceSqrtOfIsCoerciveCLM K hc hcoer hKsymm)
      dist (2 / Real.sqrt c) θ := by
  have h := physicalShiftedCovarianceFamily_stieltjes_exponentialKernelBound
    dist hsymm htri hself hθ hM hc hNR hrange hbound hcoer hbudget
  rw [stieltjesIntegralOperator_shifted_eq_covarianceSqrt
    K hc hcoer hKsymm] at h
  exact h

/-- End-to-end assembly of the physical localized covariance-root certificate:
the root kernel field is discharged by the shift-uniform Stieltjes theorem. -/
theorem physicalLocalizedCovarianceRootCertificate_of_shiftUniform
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (hself : ∀ p, dist p p = 0)
    {θ : ℝ} (hθ : 0 < θ) {R NR : ℕ} {M c covNormBound : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {K : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc}
    {covWeight : PhysicalBond d N → PhysicalBond d N → ℝ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hcoer : IsCoerciveCLM K c) (hKsymm : K.IsSymmetric)
    (hcov : PhysicalLocalizedCovarianceCertificate
      K (covarianceOfIsCoerciveCLM K hc hcoer) covNormBound covWeight)
    (hbudget : M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c / 2) :
    PhysicalLocalizedCovarianceRootCertificate
      K (covarianceOfIsCoerciveCLM K hc hcoer)
      (covarianceSqrtOfIsCoerciveCLM K hc hcoer hKsymm)
      covNormBound (Real.sqrt c⁻¹) covWeight
      (fun target source =>
        2 / Real.sqrt c * Real.exp (-(θ * (dist target source : ℝ)))) := by
  apply physicalLocalizedCovarianceRootCertificate_of_coercive_precision
    hc hcoer hKsymm hcov
  exact physicalCovarianceKernelBound_of_exponential _ dist
    (physicalCovarianceSqrt_exponentialKernelBound_of_shiftUniform
      dist hsymm htri hself hθ hM hc hNR hrange hbound hcoer hKsymm hbudget)

end

end YangMills.RG
