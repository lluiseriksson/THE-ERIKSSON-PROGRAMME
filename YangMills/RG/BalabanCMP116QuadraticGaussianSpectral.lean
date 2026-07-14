/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116GaussianOrthogonal

/-!
# CMP116 quadratic Gaussian integral: spectral-coordinate stage

This module consumes orthogonal invariance and the normalized diagonal identity.
It evaluates the quadratic Gaussian integral in an arbitrary real orthonormal
basis, for a positive diagonal spectrum.  The complex source remains bilinear:
the exponent contains `c i ^ 2`, never `‖c i‖²` or complex conjugation.

The next layer may instantiate the basis and spectrum with those of a real
symmetric positive-definite matrix and identify the product with its determinant
and the spectral sum with its inverse quadratic form.  Those identifications,
the Balaban source term, and estimate (2.26) are not claimed here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- Exact quadratic Gaussian identity in arbitrary orthonormal spectral
coordinates.  Positivity of `lam` is precisely the shifted diagonal condition
needed by the normalized product theorem. -/
theorem integral_cexp_orthogonalDiagonal_standardGaussianPi
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι))
    (lam : ι → ℝ) (c : ι → ℂ) (hlam : ∀ i, 0 < lam i) :
    ∫ x : ι → ℝ,
        Complex.exp
          (-∑ i, ((lam i - 1 : ℝ) : ℂ) / 2 *
              ((b.repr (WithLp.toLp 2 x) i : ℝ) : ℂ) ^ 2 +
            ∑ i, c i * ((b.repr (WithLp.toLp 2 x) i : ℝ) : ℂ))
        ∂(standardGaussianPi ι) =
      ((Real.sqrt (∏ i, lam i))⁻¹ : ℝ) •
        Complex.exp (∑ i, (c i) ^ 2 / (2 * lam i)) := by
  let f : (ι → ℝ) → ℂ := fun y =>
    Complex.exp
      (-∑ i, ((lam i - 1 : ℝ) : ℂ) / 2 * (y i : ℂ) ^ 2 +
        ∑ i, c i * y i)
  let qraw : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).trans
      (b.repr.toMeasurableEquiv.trans
        (MeasurableEquiv.toLp 2 (ι → ℝ)).symm)
  have hmp : MeasurePreserving qraw
      (standardGaussianPi ι) (standardGaussianPi ι) := by
    simpa [qraw] using standardGaussianPi_measurePreserving_orthogonal b.repr
  calc
    (∫ x : ι → ℝ,
        Complex.exp
          (-∑ i, ((lam i - 1 : ℝ) : ℂ) / 2 *
              ((b.repr (WithLp.toLp 2 x) i : ℝ) : ℂ) ^ 2 +
            ∑ i, c i * ((b.repr (WithLp.toLp 2 x) i : ℝ) : ℂ))
        ∂(standardGaussianPi ι)) =
      ∫ x : ι → ℝ, f x ∂(standardGaussianPi ι) := by
        simpa [qraw, f] using hmp.integral_comp' f
    _ = _ := by
      unfold standardGaussianPi
      simpa [f] using
        integral_cexp_diagonalQuadratic_standardGaussianPi_normalized
          (fun i => lam i - 1) c (fun i => by linarith [hlam i])

end

end YangMills.RG
