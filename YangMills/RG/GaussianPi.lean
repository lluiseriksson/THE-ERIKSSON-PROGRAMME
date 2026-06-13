/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

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

end YangMills.RG
