/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.RG.GaussianMGF
import YangMills.RG.KernelSchur
import YangMills.RG.CovarianceKernel

/-!
# The finite-dimensional multivariate Gaussian as an `IsGaussian` measure (gauge-RG substrate)

`docs/BALABAN-SOURCE-BOUNDS.md`.  The Bałaban small-field fluctuation integral is
an integral against a *Gaussian field on a finite lattice* — concretely, a centered
Gaussian measure on `ι → ℝ` (`ι` the finite set of lattice sites/links) with a
prescribed covariance.  Mathlib provides the one-dimensional `gaussianReal`, the
abstract predicate `IsGaussian`, and the joint-Gaussianity of independent Gaussians,
but **no concrete multivariate Gaussian measure** as an `IsGaussian` instance.  This
file supplies the missing primitive.

* **`isGaussian_pi`** — the product of one-dimensional Gaussians,
  `Measure.pi (fun i => gaussianReal (m i) (v i))` on `ι → ℝ` (`[Fintype ι]`), is a
  genuine `IsGaussian` measure.  This is the standard multivariate Gaussian with
  diagonal covariance `diag v` and mean `m`.  Proof: the coordinate projections are
  independent (`iIndepFun_pi`) and each is one-dimensional Gaussian
  (`pi_map_eval` + `isGaussian_gaussianReal`), hence *jointly* Gaussian
  (`iIndepFun.hasGaussianLaw`); the joint law of the coordinates is the identity
  pushforward, which is the measure itself.

* **`isGaussian_pi_map_clm`** — pushing the standard multivariate Gaussian forward
  through **any continuous linear map** `A : (ι → ℝ) →L[ℝ] F` yields an `IsGaussian`
  measure on `F`.  This is the constructive Gaussian-with-prescribed-covariance route:
  choosing `A` a square-root / Cholesky factor of a target PSD covariance `C` realizes
  a centered Gaussian whose covariance bilinear form is `A ∘ Aᵀ` — the field the
  Bałaban fluctuation integral integrates against, now an honest `IsGaussian` object
  rather than a carried hypothesis.

**Honest scope.**  This constructs the *abstract* finite-dimensional Gaussian measure
and shows it is closed under linear images.  It does **not** prove `hRpoly`, and it
does not by itself match `A ∘ Aᵀ` to a specific Bałaban background-field covariance
(that is the separate Cholesky/spectral-factor + propagator-bound step).  It removes
the "no constructive Gaussian measure" obstruction flagged in the previous campaign:
`gaussian_exp_integral_le_isGaussian` (`RG/GaussianMGF.lean`) now has concrete,
non-abstract `IsGaussian` measures to consume.

**Source.**  Mathlib's `ProbabilityTheory.iIndepFun.hasGaussianLaw` (independent
Gaussians are jointly Gaussian), `iIndepFun_pi`, `Measure.pi_map_eval`,
`isGaussian_map_of_measurable`; the application is Bałaban CMP 95/109's small-field
integral; strategy/framing Lluis Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace YangMills.RG

/-- **The finite-dimensional multivariate Gaussian is `IsGaussian`.**  The product
measure `Measure.pi (fun i => gaussianReal (m i) (v i))` on `ι → ℝ` (with `ι` finite)
— the standard multivariate Gaussian with mean `m` and diagonal covariance `diag v` —
is a genuine Gaussian measure in Mathlib's sense.  Mathlib has the 1-D `gaussianReal`
and the abstract `IsGaussian` predicate but no concrete multivariate Gaussian; this is
that missing primitive.  Built from coordinate independence (`iIndepFun_pi`), the
1-D coordinate marginals (`pi_map_eval`), and the joint Gaussianity of independent
Gaussians (`iIndepFun.hasGaussianLaw`). -/
theorem isGaussian_pi {ι : Type*} [Fintype ι] (m : ι → ℝ) (v : ι → NNReal) :
    IsGaussian (Measure.pi (fun i => gaussianReal (m i) (v i))) := by
  classical
  have hX1 : ∀ i, HasGaussianLaw (fun ω : ι → ℝ => ω i)
      (Measure.pi (fun i => gaussianReal (m i) (v i))) := by
    intro i
    refine ⟨?_⟩
    rw [show (fun ω : ι → ℝ => ω i) = Function.eval i from rfl, Measure.pi_map_eval]
    rw [Finset.prod_eq_one (fun j _ => measure_univ), one_smul]
    exact isGaussian_gaussianReal (m i) (v i)
  have hX2 : iIndepFun (fun (i : ι) (ω : ι → ℝ) => ω i)
      (Measure.pi (fun i => gaussianReal (m i) (v i))) :=
    iIndepFun_pi (X := fun _ => id) (fun i => aemeasurable_id)
  have hjoint := hX2.hasGaussianLaw hX1
  have hG := hjoint.isGaussian_map
  rwa [show (fun (ω : ι → ℝ) => (fun i => ω i)) = (id : (ι → ℝ) → (ι → ℝ)) from rfl,
    Measure.map_id] at hG

/-- **Linear images of the multivariate Gaussian are Gaussian.**  For any continuous
linear map `A : (ι → ℝ) →L[ℝ] F`, the pushforward of the standard multivariate
Gaussian under `A` is again an `IsGaussian` measure on `F`.  Taking `A` to be a
square-root / Cholesky factor of a target positive-semidefinite covariance realizes a
centered Gaussian field with that covariance (its covariance bilinear form is
`A ∘ Aᵀ`) — the constructive Gaussian-from-covariance object the small-field
fluctuation integral integrates against. -/
theorem isGaussian_pi_map_clm {ι : Type*} [Fintype ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] [CompleteSpace F]
    (m : ι → ℝ) (v : ι → NNReal) (A : (ι → ℝ) →L[ℝ] F) :
    IsGaussian ((Measure.pi (fun i => gaussianReal (m i) (v i))).map A) := by
  haveI : IsGaussian (Measure.pi (fun i => gaussianReal (m i) (v i))) := isGaussian_pi m v
  exact isGaussian_map_of_measurable A.continuous.measurable

/-- **The standard centered multivariate Gaussian is centered.**  For
`μ = Measure.pi (fun i => gaussianReal 0 (v i))` (mean-zero coordinates) and any
continuous linear functional `L`, the mean `μ[L] = 0`.  Proof by symmetry: each
`gaussianReal 0 (v i)` is invariant under `x ↦ -x` (`gaussianReal_map_neg`,
`neg_zero`), so the product measure is too (`Measure.pi_map_pi`); hence
`μ[L] = μ[L ∘ (-·)] = -μ[L]` (`L` linear, `IsGaussian.integrable_dual` for
integrability), forcing `μ[L] = 0`.  This discharges the centering hypothesis of
`gaussian_exp_integral_le_isGaussian`. -/
theorem pi_gaussian_centered {ι : Type*} [Fintype ι] (v : ι → NNReal)
    (L : StrongDual ℝ (ι → ℝ)) :
    (Measure.pi (fun i => gaussianReal 0 (v i)))[L] = 0 := by
  classical
  haveI : IsGaussian (Measure.pi (fun i => gaussianReal 0 (v i))) :=
    isGaussian_pi (fun _ => 0) v
  have hsymm : (Measure.pi (fun i => gaussianReal 0 (v i))).map (fun x : ι → ℝ => -x)
      = Measure.pi (fun i => gaussianReal 0 (v i)) := by
    rw [show (fun x : ι → ℝ => -x) = (fun (x : ι → ℝ) i => -(x i)) from rfl,
      Measure.pi_map_pi (fun _ => measurable_neg.aemeasurable)]
    have hfac : (fun i => (gaussianReal (0 : ℝ) (v i)).map (fun x => -x))
        = (fun i => gaussianReal (0 : ℝ) (v i)) := by
      funext i; rw [gaussianReal_map_neg, neg_zero]
    rw [hfac]
  have key : (Measure.pi (fun i => gaussianReal 0 (v i)))[L]
      = -(Measure.pi (fun i => gaussianReal 0 (v i)))[L] := by
    conv_lhs => rw [← hsymm]
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [map_neg, integral_neg]
  linarith [key]

/-- **Concrete field-size / MGF bound on the standard multivariate Gaussian.**
Combining `isGaussian_pi` (the constructed measure), `pi_gaussian_centered` (the
centering), and `gaussian_exp_integral_le_isGaussian` (the abstract bound): for
the centered standard multivariate Gaussian on `ι → ℝ` and any continuous linear
observable `L` with variance bounded by `B`, the exponential field-size integral
is bounded, `∫ exp(L φ) dμ ≤ exp(B/2)`.  Unlike the abstract bound, this is
instantiated on a genuine constructed `IsGaussian` measure — fully non-vacuous.
With the kernel/Schur/PSD substrate supplying `Var[L; μ] ≤ a·S·‖L‖²`, this is the
small-field fluctuation-integral input on an explicit Gaussian field. -/
theorem pi_gaussian_exp_integral_le {ι : Type*} [Fintype ι] (v : ι → NNReal)
    (L : StrongDual ℝ (ι → ℝ)) {B : ℝ}
    (hvar : Var[L; Measure.pi (fun i => gaussianReal 0 (v i))] ≤ B) :
    ∫ x, Real.exp (L x) ∂(Measure.pi (fun i => gaussianReal 0 (v i)))
      ≤ Real.exp (B / 2) := by
  haveI : IsGaussian (Measure.pi (fun i => gaussianReal 0 (v i))) :=
    isGaussian_pi (fun _ => 0) v
  exact gaussian_exp_integral_le_isGaussian L (pi_gaussian_centered v L) hvar

set_option maxHeartbeats 1000000 in
/-- **The variance bridge: the covariance form of the standard multivariate
Gaussian, explicitly computed.**  For `μ = Measure.pi (fun i => gaussianReal 0 vᵢ)`
and any continuous linear observable `L`, the variance of `L` is the diagonal
quadratic form `Var[L; μ] = ∑ᵢ (L eᵢ)²·vᵢ`, where `eᵢ = Pi.single i 1` is the
`i`-th coordinate vector.  Proof: write `L = ∑ᵢ (L eᵢ)·(·ᵢ)` (`Finset.univ_sum_single`
+ linearity), the coordinates are independent (`iIndepFun_pi`) and square-integrable
(`IsGaussian.memLp_dual`), so the variance of the sum splits
(`IndepFun.variance_sum`); each term contributes `(L eᵢ)²·Var[(·ᵢ)] = (L eᵢ)²·vᵢ`
(`variance_const_mul` + `variance_id_gaussianReal` via the coordinate marginal).
This is the linchpin connecting the kernel/Schur covariance substrate to the
Gaussian field-size bound: the covariance form is now a concrete sum, bounded by
the Schur/PSD machinery. -/
theorem pi_gaussian_variance {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → NNReal)
    (L : StrongDual ℝ (ι → ℝ)) :
    Var[L; Measure.pi (fun i => gaussianReal 0 (v i))]
      = ∑ i, (L (Pi.single i 1)) ^ 2 * (v i : ℝ) := by
  set μ : Measure (ι → ℝ) := Measure.pi (fun i => gaussianReal 0 (v i)) with hμ
  haveI : IsGaussian μ := isGaussian_pi (fun _ => 0) v
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set X : ι → (ι → ℝ) → ℝ := fun i ω => (L (Pi.single i 1)) * ω i with hX
  have hLrep : (⇑L) = ∑ i, X i := by
    funext ω
    have h1 : (∑ i, Pi.single i (ω i)) = ω := Finset.univ_sum_single ω
    have hsum : L ω = ∑ i, (L (Pi.single i 1)) * ω i := by
      conv_lhs => rw [← h1]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hsm : (Pi.single i (ω i) : ι → ℝ) = (ω i) • (Pi.single i (1 : ℝ) : ι → ℝ) := by
        funext j; rcases eq_or_ne j i with h | h <;> simp [Pi.single_apply, h]
      rw [hsm, map_smul, smul_eq_mul, mul_comm]
    rw [hsum]; simp [hX, Finset.sum_apply]
  have hcoordvar : ∀ i, Var[fun ω : ι → ℝ => ω i; μ] = (v i : ℝ) := by
    intro i
    have hmap : μ.map (fun ω : ι → ℝ => ω i) = gaussianReal 0 (v i) := by
      rw [hμ, show (fun ω : ι → ℝ => ω i) = Function.eval i from rfl, Measure.pi_map_eval,
        Finset.prod_eq_one (fun j _ => measure_univ), one_smul]
    rw [← variance_id_map (measurable_pi_apply i).aemeasurable, hmap]
    exact variance_id_gaussianReal
  have hmem : ∀ i, MemLp (X i) 2 μ := by
    intro i
    have hproj : MemLp (fun ω : ι → ℝ => ω i) 2 μ := by
      have := IsGaussian.memLp_dual μ
        (ContinuousLinearMap.proj i : StrongDual ℝ (ι → ℝ)) 2 (by simp)
      simpa using this
    have := hproj.const_mul (L (Pi.single i 1))
    simpa [hX] using this
  have hpair : Set.Pairwise (↑(Finset.univ : Finset ι)) (fun i j => X i ⟂ᵢ[μ] X j) := by
    intro i _ j _ hij
    have hcoord : IndepFun (fun ω : ι → ℝ => ω i) (fun ω : ι → ℝ => ω j) μ := by
      have := (iIndepFun_pi (μ := fun i => gaussianReal 0 (v i)) (X := fun _ => id)
        (fun _ => aemeasurable_id)).indepFun hij
      simpa using this
    have := hcoord.comp (measurable_id.const_mul (L (Pi.single i 1)))
      (measurable_id.const_mul (L (Pi.single j 1)))
    simpa [hX, Function.comp] using this
  calc Var[L; μ] = Var[∑ i, X i; μ] := by rw [hLrep]
    _ = ∑ i, Var[X i; μ] := IndepFun.variance_sum (fun i _ => hmem i) hpair
    _ = ∑ i, (L (Pi.single i 1)) ^ 2 * (v i : ℝ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hvi : Var[X i; μ]
            = (L (Pi.single i 1)) ^ 2 * Var[fun ω : ι → ℝ => ω i; μ] :=
          variance_const_mul (L (Pi.single i 1)) (fun ω => ω i) μ
        rw [hvi, hcoordvar i]

/-- **Field-size bound from the explicit covariance sum.**  Combining
`pi_gaussian_variance` with `pi_gaussian_exp_integral_le`: if the explicit
diagonal covariance form `∑ᵢ (L eᵢ)²·vᵢ` is bounded by `B`, then
`∫ exp(L φ) dμ ≤ exp(B/2)`.  The "variance bound ⟹ MGF bound" link with the
variance now *computed*, ready for the Schur/PSD covariance bound to supply `B`. -/
theorem pi_gaussian_exp_integral_le_of_covariance_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → NNReal) (L : StrongDual ℝ (ι → ℝ)) {B : ℝ}
    (hB : ∑ i, (L (Pi.single i 1)) ^ 2 * (v i : ℝ) ≤ B) :
    ∫ x, Real.exp (L x) ∂(Measure.pi (fun i => gaussianReal 0 (v i)))
      ≤ Real.exp (B / 2) := by
  have hvar : Var[L; Measure.pi (fun i => gaussianReal 0 (v i))] ≤ B := by
    rw [pi_gaussian_variance v L]; exact hB
  exact pi_gaussian_exp_integral_le v L hvar

/-- **Field-size bound from a uniform covariance (variance) bound.**  If every
coordinate variance is bounded, `vᵢ ≤ a`, then
`∫ exp(L φ) dμ ≤ exp(a·(∑ᵢ (L eᵢ)²)/2)`.  This is the small-field
fluctuation-integral input in its canonical shape `exp(½ a·‖·‖²)`: a uniform
bound on the (diagonal) covariance gives uniform exponential moments.  The
`a := a·S` of the Schur bound `expDecay_quadratic_form_le` / `psd_cauchy_schwarz`
plugs directly into the `a` here. -/
theorem pi_gaussian_exp_integral_le_of_uniform_variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → NNReal) (a : ℝ) (ha : ∀ i, (v i : ℝ) ≤ a) (L : StrongDual ℝ (ι → ℝ)) :
    ∫ x, Real.exp (L x) ∂(Measure.pi (fun i => gaussianReal 0 (v i)))
      ≤ Real.exp (a * (∑ i, (L (Pi.single i 1)) ^ 2) / 2) := by
  refine pi_gaussian_exp_integral_le_of_covariance_sum v L ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [mul_comm a]
  exact mul_le_mul_of_nonneg_left (ha i) (sq_nonneg _)

/-- **Variance of the linearly-transformed Gaussian (general / off-diagonal
covariance).**  Pushing the standard multivariate Gaussian through a continuous
linear map `A : (ι → ℝ) →L[ℝ] F`, the variance of any dual `L` on `F` is
`Var[L; μ.map A] = ∑ᵢ (L (A eᵢ))²·vᵢ`.  This is the genuine covariance form of
the constructed field with covariance `A∘Aᵀ` (off-diagonal in general) — the
realistic shape of the Bałaban fluctuation propagator, not just the diagonal
case.  Proof: `variance_map` turns it into `Var[L∘A; μ]`, then
`pi_gaussian_variance` applied to the composite dual `L∘L A`. -/
theorem pi_gaussian_map_variance {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] [CompleteSpace F]
    (v : ι → NNReal) (A : (ι → ℝ) →L[ℝ] F) (L : StrongDual ℝ F) :
    Var[L; (Measure.pi (fun i => gaussianReal 0 (v i))).map A]
      = ∑ i, (L (A (Pi.single i 1))) ^ 2 * (v i : ℝ) := by
  rw [variance_map (by fun_prop) (by fun_prop), ← ContinuousLinearMap.coe_comp',
    pi_gaussian_variance v (L.comp A)]
  simp [ContinuousLinearMap.comp_apply]

/-- **Field-size bound for the linearly-transformed (general-covariance)
Gaussian.**  For the Gaussian field `μ.map A` (covariance `A∘Aᵀ`) and any dual
`L` with `∑ᵢ (L (A eᵢ))²·vᵢ ≤ B`, the exponential field-size integral is bounded,
`∫ exp(L φ) d(μ.map A) ≤ exp(B/2)`.  Centering is automatic
(`pi_gaussian_centered` transported through `A`); the variance is the explicit
form of `pi_gaussian_map_variance`.  This is the small-field fluctuation-integral
bound for an arbitrary (off-diagonal) constructed Gaussian covariance. -/
theorem pi_gaussian_map_exp_integral_le {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] [CompleteSpace F]
    (v : ι → NNReal) (A : (ι → ℝ) →L[ℝ] F) (L : StrongDual ℝ F) {B : ℝ}
    (hB : ∑ i, (L (A (Pi.single i 1))) ^ 2 * (v i : ℝ) ≤ B) :
    ∫ x, Real.exp (L x) ∂((Measure.pi (fun i => gaussianReal 0 (v i))).map A)
      ≤ Real.exp (B / 2) := by
  haveI : IsGaussian ((Measure.pi (fun i => gaussianReal 0 (v i))).map A) :=
    isGaussian_pi_map_clm (fun _ => 0) v A
  have hcenter : ((Measure.pi (fun i => gaussianReal 0 (v i))).map A)[L] = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    have hcomp : (fun x => L (A x)) = (⇑(L.comp A)) := by
      funext x; simp [ContinuousLinearMap.comp_apply]
    rw [hcomp]
    exact pi_gaussian_centered v (L.comp A)
  have hvar : Var[L; (Measure.pi (fun i => gaussianReal 0 (v i))).map A] ≤ B := by
    rw [pi_gaussian_map_variance v A L]; exact hB
  exact gaussian_exp_integral_le_isGaussian L hcenter hvar

set_option maxHeartbeats 1000000 in
/-- **The covariance of the transformed Gaussian is the Gram quadratic form of its
kernel.**  For the field `μ.map A`, the variance of a dual `L` is the quadratic
form `Var[L; μ.map A] = ∑ₓ∑ᵧ cₓ·Kₓᵧ·cᵧ` of the (Gram) covariance kernel
`Kₓᵧ = ∑ᵢ vᵢ·(A eᵢ)ₓ·(A eᵢ)ᵧ` evaluated at the coefficient vector `cₓ = L eₓ`.
(`set_option maxHeartbeats` raised for the triple-sum reorganization.)
This puts the covariance into the exact shape consumed by the Schur quadratic-form
bound `expDecay_quadratic_form_le`.  Proof: expand `L (A eᵢ) = ∑ₓ (A eᵢ)ₓ·cₓ`,
square, and reorganize the triple sum (`Finset.sum_mul_sum`, `Finset.sum_comm`). -/
theorem pi_gaussian_map_variance_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → NNReal) (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (L : StrongDual ℝ (ι → ℝ)) :
    Var[L; (Measure.pi (fun i => gaussianReal 0 (v i))).map A]
      = ∑ x, ∑ y, (L (Pi.single x 1))
          * (∑ i, (v i : ℝ) * ((A (Pi.single i 1)) x * (A (Pi.single i 1)) y))
          * (L (Pi.single y 1)) := by
  rw [pi_gaussian_map_variance v A L]
  have hLA : ∀ i, L (A (Pi.single i 1))
      = ∑ x, (A (Pi.single i 1)) x * L (Pi.single x 1) := by
    intro i
    conv_lhs => rw [← Finset.univ_sum_single (A (Pi.single i 1)), map_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hsm : (Pi.single x ((A (Pi.single i 1)) x) : ι → ℝ)
        = ((A (Pi.single i 1)) x) • (Pi.single x (1 : ℝ) : ι → ℝ) := by
      funext j; rcases eq_or_ne j x with h | h <;> simp [Pi.single_apply, h]
    rw [hsm, map_smul, smul_eq_mul]
  have step : ∀ i, (L (A (Pi.single i 1))) ^ 2 * (v i : ℝ)
      = ∑ x, ∑ y, (L (Pi.single x 1))
          * ((v i : ℝ) * ((A (Pi.single i 1)) x * (A (Pi.single i 1)) y))
          * (L (Pi.single y 1)) := by
    intro i
    rw [hLA i, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y _ => by ring)
  rw [Finset.sum_congr rfl (fun i _ => step i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]

/-- **The faithful closure: an exponentially-decaying covariance kernel gives the
Gaussian field-size bound.**  If the Gram covariance kernel
`Kₓᵧ = ∑ᵢ vᵢ·(A eᵢ)ₓ·(A eᵢ)ᵧ` of the field `μ.map A` is exponentially decaying
(`ExpDecay d a κ K`, symmetric metric `d`, row-sum `≤ S`), then
`∫ exp(L z) d(μ.map A) ≤ exp(a·S·(∑ₓ (L eₓ)²)/2)`.  This is the end-to-end
"ExpDecay covariance kernel ⟹ small-field fluctuation bound" on a genuine
constructed Gaussian: the variance is the kernel quadratic form
(`pi_gaussian_map_variance_quadratic`), bounded by the finite-dimensional Schur
test (`expDecay_quadratic_form_le`, `RG/KernelSchur.lean`), feeding the field-size
bound.  The decay constants `(a, κ, S)` are exactly those the Combes–Thomas /
gauge-propagator analysis supplies for the Bałaban background-field covariance. -/
theorem pi_gaussian_map_exp_integral_le_of_expDecay {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → NNReal) (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (L : StrongDual ℝ (ι → ℝ))
    {d : ι → ι → ℝ} {a κ S : ℝ} (ha : 0 ≤ a) (hsym : ∀ x y, d x y = d y x)
    (hA : ExpDecay d a κ
      (fun x y => ∑ i, (v i : ℝ) * ((A (Pi.single i 1)) x * (A (Pi.single i 1)) y)))
    (hrow : ∀ x, ∑ y, Real.exp (-κ * d x y) ≤ S) :
    ∫ z, Real.exp (L z) ∂((Measure.pi (fun i => gaussianReal 0 (v i))).map A)
      ≤ Real.exp (a * S * (∑ x, (L (Pi.single x 1)) ^ 2) / 2) := by
  refine pi_gaussian_map_exp_integral_le v A L ?_
  calc ∑ i, (L (A (Pi.single i 1))) ^ 2 * (v i : ℝ)
      = ∑ x, ∑ y, (L (Pi.single x 1))
          * (∑ i, (v i : ℝ) * ((A (Pi.single i 1)) x * (A (Pi.single i 1)) y))
          * (L (Pi.single y 1)) := by
        rw [← pi_gaussian_map_variance v A L, pi_gaussian_map_variance_quadratic v A L]
    _ ≤ a * S * ∑ x, (L (Pi.single x 1)) ^ 2 :=
        le_trans (le_abs_self _)
          (expDecay_quadratic_form_le ha hsym hA hrow (fun x => L (Pi.single x 1)))

/-- **The constructed Gram covariance kernel is a genuine PSD kernel.**  The
covariance kernel `Kₓᵧ = ∑ᵢ vᵢ·(A eᵢ)ₓ·(A eᵢ)ᵧ` of the transformed Gaussian
`μ.map A` satisfies `IsPSDKernel` (`RG/CovarianceKernel.lean`): every quadratic
form `∑ₓ∑ᵧ uₓ·Kₓᵧ·uᵧ ≥ 0`.  This certifies that the Gram construction always
yields a valid covariance — the non-vacuity witness tying the constructed
Gaussian to the PSD-kernel interface (`psd_cauchy_schwarz` etc.).  Proof: any
coefficient vector `u` is realized by the dual `L = ∑ₓ uₓ·projₓ` (so `L eₓ = uₓ`),
whence the quadratic form equals `Var[L; μ.map A] ≥ 0`
(`pi_gaussian_map_variance_quadratic` + `variance_nonneg`). -/
theorem gram_kernel_isPSDKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → NNReal) (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    IsPSDKernel
      (fun x y => ∑ i, (v i : ℝ) * ((A (Pi.single i 1)) x * (A (Pi.single i 1)) y)) := by
  intro u
  set L : StrongDual ℝ (ι → ℝ) := ∑ x, (u x) • (ContinuousLinearMap.proj x) with hLdef
  have hLe : ∀ y, L (Pi.single y 1) = u y := by
    intro y
    simp [hLdef, ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply,
      Pi.single_apply]
  have hnn := variance_nonneg (⇑L) ((Measure.pi (fun i => gaussianReal 0 (v i))).map A)
  rw [pi_gaussian_map_variance_quadratic v A L] at hnn
  simpa only [hLe] using hnn

end YangMills.RG
