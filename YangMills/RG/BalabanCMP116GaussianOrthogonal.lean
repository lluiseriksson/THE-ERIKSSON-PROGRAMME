/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116QuadraticGaussian
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# CMP116 quadratic Gaussian integral: orthogonal stage

This module proves that the finite-dimensional standard Gaussian product is
preserved by every real linear isometry.  The proof is intrinsic: its
characteristic function depends only on the Euclidean norm, so uniqueness of
characteristic functions gives invariance under orthogonal changes of basis.

This is the exact change-of-variables interface needed to transport the
diagonal quadratic identity through the spectral basis of a real symmetric
matrix.  No determinant identity, matrix diagonalization, Balaban source-term
identification, or estimate (2.26) is claimed here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- The raw finite product of centered real standard Gaussians. -/
noncomputable def standardGaussianPi (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 (1 : NNReal))

instance {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (standardGaussianPi ι) := by
  unfold standardGaussianPi
  infer_instance

/-- The same Gaussian product transported to the Euclidean `L²` model. -/
noncomputable def standardGaussianEuclidean (ι : Type*) [Fintype ι] :
    Measure (EuclideanSpace ℝ ι) :=
  (standardGaussianPi ι).map (WithLp.toLp 2)

instance {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (standardGaussianEuclidean ι) := by
  unfold standardGaussianEuclidean
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The characteristic function of the standard Euclidean Gaussian is radial. -/
theorem charFun_standardGaussianEuclidean
    {ι : Type*} [Fintype ι] (t : EuclideanSpace ℝ ι) :
    charFun (standardGaussianEuclidean ι) t =
      Complex.exp (-((‖t‖ ^ 2 : ℝ) : ℂ) / 2) := by
  rw [standardGaussianEuclidean, standardGaussianPi, charFun_pi]
  simp_rw [charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
    NNReal.coe_one, ← Complex.exp_sum]
  congr 2
  calc
    (∑ i, -(1 * (t.ofLp i : ℂ) ^ 2 / 2)) =
        (((-(∑ i, (t.ofLp i) ^ 2) / 2 : ℝ)) : ℂ) := by
      push_cast
      simp only [one_mul, div_eq_mul_inv,
        Finset.sum_neg_distrib, Finset.sum_mul, neg_mul]
    _ = (((-(‖t‖ ^ 2) / 2 : ℝ)) : ℂ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
    _ = -((‖t‖ ^ 2 : ℝ) : ℂ) / 2 := by
      push_cast
      rfl

/-- Every real orthogonal change of basis preserves the Euclidean standard
Gaussian measure. -/
theorem standardGaussianEuclidean_measurePreserving
    {ι : Type*} [Fintype ι]
    (Q : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurePreserving Q
      (standardGaussianEuclidean ι) (standardGaussianEuclidean ι) := by
  refine ⟨Q.continuous.measurable, ?_⟩
  apply Measure.ext_of_charFun
  funext t
  rw [charFun]
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [Q.inner_map_eq_flip]
  change charFun (standardGaussianEuclidean ι) (Q.symm t) =
    charFun (standardGaussianEuclidean ι) t
  rw [charFun_standardGaussianEuclidean,
    charFun_standardGaussianEuclidean, Q.symm.norm_map]

/-- Raw-coordinate form of orthogonal invariance for the standard Gaussian
product on `ι → ℝ`. -/
theorem standardGaussianPi_measurePreserving_orthogonal
    {ι : Type*} [Fintype ι]
    (Q : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurePreserving
      (fun x : ι → ℝ => WithLp.ofLp (Q (WithLp.toLp 2 x)))
      (standardGaussianPi ι) (standardGaussianPi ι) := by
  let e : (ι → ℝ) ≃ᵐ EuclideanSpace ℝ ι :=
    MeasurableEquiv.toLp 2 (ι → ℝ)
  have hto : MeasurePreserving e
      (standardGaussianPi ι) (standardGaussianEuclidean ι) := by
    refine ⟨by fun_prop, ?_⟩
    rfl
  exact hto.symm.comp
    ((standardGaussianEuclidean_measurePreserving Q).comp hto)

end

end YangMills.RG
