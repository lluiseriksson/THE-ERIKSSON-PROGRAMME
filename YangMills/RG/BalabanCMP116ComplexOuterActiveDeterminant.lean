/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexOuterGaussian
import YangMills.RG.BalabanCMP116ActiveDeterminantBound

/-!
# Active-rank bound for the global complex outer Gaussian

The complex `R1` quadratic acts on the full outer field, but its symmetric
real correction can still factor through a finite source-active state.  This
module turns such a rectangular factorization into a determinant lower bound
whose exponent is the active cardinality.

This is the source-faithful replacement for pointwise coordinate support:
the matrix may have nonzero tails on the ambient field, while its nontrivial
determinant is nevertheless finite-rank.
-/

namespace YangMills.RG

open Matrix MeasureTheory

noncomputable section

open scoped Matrix.Norms.Operator

/-- A complex rectangular factorization of the negative symmetric real
correction localizes the shifted determinant to the active intermediate
type. -/
theorem one_sub_norm_pow_activeCard_le_det_shifted_symmetricRealPart
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ]
    (H : Matrix ι ι ℝ)
    (L : Matrix ι κ ℂ) (R : Matrix κ ι ℂ)
    (hpos : (1 - H).PosDef)
    (hfactor : (-H).map Complex.ofRealHom = L * R)
    (hsmall : ‖L * R‖ < 1) :
    (1 - ‖L * R‖) ^ Fintype.card κ ≤ Matrix.det (1 - H) := by
  have hactive :
      (1 - ‖L * R‖) ^ Fintype.card κ ≤
        ‖(1 + R * L).det‖ :=
    Matrix.one_sub_norm_pow_card_le_norm_det_one_add_rectangular_mul
      L R hsmall
  have hmap :
      (1 - H).map Complex.ofRealHom = 1 + L * R := by
    calc
      (1 - H).map Complex.ofRealHom =
          1 + (-H).map Complex.ofRealHom := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp
          ring
        · simp [hij]
      _ = 1 + L * R := by rw [hfactor]
  have hdetMap :
      ((1 - H).map Complex.ofRealHom).det =
        Complex.ofReal (Matrix.det (1 - H)) := by
    change
      (Complex.ofRealHom.mapMatrix (1 - H)).det =
        Complex.ofRealHom (Matrix.det (1 - H))
    rw [← Complex.ofRealHom.map_det]
  have hdetNorm :
      ‖(1 + L * R).det‖ = Matrix.det (1 - H) := by
    rw [← hmap, hdetMap, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos.det_pos]
  rw [← Matrix.det_one_add_mul_comm L R, hdetNorm] at hactive
  exact hactive

/-- Exact outer-Gaussian integration followed by active-rank determinant
localization.  The exponent is `card κ`, even though the quadratic acts on
the complete ambient field `ι`. -/
theorem integral_exp_re_complexQuadratic_le_activeCard
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ)
    (L : Matrix ι κ ℂ) (R : Matrix κ ι ℂ)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart A).PosDef)
    (hfactor :
      (-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
          Complex.ofRealHom =
        L * R)
    (hsmall : ‖L * R‖ < 1) :
    (∫ x : ι → ℝ,
        Real.exp ((cmp116Eq214ComplexQuadratic A x).re)
        ∂standardGaussianPi ι) ≤
      (Real.sqrt
        ((1 - ‖L * R‖) ^ Fintype.card κ))⁻¹ := by
  let H := cmp116Eq214ComplexQuadraticSymmetricRealPart A
  have hdetLower :
      (1 - ‖L * R‖) ^ Fintype.card κ ≤ Matrix.det (1 - H) := by
    exact
      one_sub_norm_pow_activeCard_le_det_shifted_symmetricRealPart
        H L R (by simpa [H] using hpos) (by simpa [H] using hfactor)
          hsmall
  have hbase : 0 < 1 - ‖L * R‖ := sub_pos.mpr hsmall
  have hlower :
      0 < (1 - ‖L * R‖) ^ Fintype.card κ := pow_pos hbase _
  have hdet : 0 < Matrix.det (1 - H) := by
    exact hpos.det_pos
  have hsqrt :
      Real.sqrt ((1 - ‖L * R‖) ^ Fintype.card κ) ≤
        Real.sqrt (Matrix.det (1 - H)) :=
    Real.sqrt_le_sqrt hdetLower
  have hinv :
      (Real.sqrt (Matrix.det (1 - H)))⁻¹ ≤
        (Real.sqrt
          ((1 - ‖L * R‖) ^ Fintype.card κ))⁻¹ := by
    exact
      (inv_le_inv₀ (Real.sqrt_pos.2 hdet)
        (Real.sqrt_pos.2 hlower)).2 hsqrt
  rw [integral_exp_re_complexQuadratic_standardGaussianPi A hpos]
  simpa [H] using hinv

end

end YangMills.RG
