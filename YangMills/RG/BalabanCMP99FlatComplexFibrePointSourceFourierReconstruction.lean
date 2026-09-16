/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FlatPhysicalFibreDFT

/-!
# Exact coarse point-source Fourier reconstruction

This neutral finite layer reconstructs one literal complex-fibre point source
from the already sealed positive Fourier modes with the exact product-volume
normalization and the inverse source character.  It then transports that
identity through an arbitrary complex continuous-linear map.

No Green, precision, physical coefficient, contour estimate, owner bound or
terminal field occurs here.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

/-- Literal point source on the finite complex physical fibre. -/
def cmp99FlatComplexFibrePointSource
    {d N Nc : ℕ} [NeZero N]
    (y : FinBox d N) (v : SUNLieComplexCoord Nc) :
    FinBox d N → SUNLieComplexCoord Nc :=
  fun x => if x = y then v else 0

/-- FinBox form of the exact product-character orthogonality relation, in
the orientation required by a point source at `y`. -/
theorem sum_cmp99FlatFourierMode_mul_inv
    {d N : ℕ} [NeZero N] (x y : FinBox d N) :
    (∑ k : FinBox d N,
        cmp99FlatFourierMode k x * (cmp99FlatFourierMode k y)⁻¹) =
      if x = y then (N : ℂ) ^ d else 0 := by
  let e := cmp99FinBoxZModEquiv d N
  let term := fun q : CMP99FlatZModBox d N =>
    cmp99FlatZModFourierCharacter q (e x) *
      cmp99FlatZModFourierCharacter (-q) (e y)
  calc
    (∑ k : FinBox d N,
        cmp99FlatFourierMode k x * (cmp99FlatFourierMode k y)⁻¹) =
      ∑ k : FinBox d N, term (e k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [cmp99FlatFourierMode_eq_finBoxFourierCharacter,
          cmp99FlatFourierMode_eq_finBoxFourierCharacter]
        rw [← cmp99FlatZModFourierCharacter_neg_left]
    _ = ∑ q : CMP99FlatZModBox d N, term q := by
      exact Equiv.sum_comp e term
    _ = if e x = e y then (N : ℂ) ^ d else 0 := by
      exact sum_cmp99FlatZModFourierCharacter_mul_neg (e x) (e y)
    _ = if x = y then (N : ℂ) ^ d else 0 := by
      by_cases hxy : x = y
      · subst y
        simp
      · rw [if_neg hxy, if_neg]
        exact fun heq => hxy (e.injective heq)

/-- Exact inverse-DFT expansion of one complex-fibre point source. -/
theorem cmp99FlatComplexFibrePointSource_eq_normalized_sum_fourierMode
    {d N Nc : ℕ} [NeZero N]
    (y : FinBox d N) (v : SUNLieComplexCoord Nc) :
    cmp99FlatComplexFibrePointSource y v =
      (((N : ℂ) ^ d)⁻¹) •
        ∑ k : FinBox d N,
          (cmp99FlatFourierMode k y)⁻¹ •
            cmp99FlatComplexFibreFourierMode k v := by
  classical
  funext x
  ext a
  let volume : ℂ := (N : ℂ) ^ d
  have hvolume : volume ≠ 0 :=
    pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hsum :
      (∑ k : FinBox d N,
          (cmp99FlatFourierMode k y)⁻¹ *
            cmp99FlatFourierMode k x) =
        if x = y then volume else 0 := by
    simpa only [mul_comm] using
      (sum_cmp99FlatFourierMode_mul_inv x y)
  simp only [cmp99FlatComplexFibrePointSource, Pi.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply,
    cmp99FlatComplexFibreFourierMode, PiLp.smul_apply, smul_eq_mul]
  have hfactor :
      (∑ k : FinBox d N,
          (cmp99FlatFourierMode k y)⁻¹ *
            (cmp99FlatFourierMode k x * v a)) =
        (∑ k : FinBox d N,
          (cmp99FlatFourierMode k y)⁻¹ *
            cmp99FlatFourierMode k x) * v a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfactor, hsum]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]
    change v a = volume⁻¹ * (volume * v a)
    rw [← mul_assoc, inv_mul_cancel₀ hvolume, one_mul]
  · rw [if_neg hxy, if_neg hxy]
    simp

/-- An arbitrary complex continuous-linear map consumes the exact point
source reconstruction without changing the normalization or Fourier
orientation. -/
theorem ContinuousLinearMap_apply_cmp99FlatComplexFibrePointSource_eq
    {d N Nc : ℕ} [NeZero N]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : (FinBox d N → SUNLieComplexCoord Nc) →L[ℂ] W)
    (y : FinBox d N) (v : SUNLieComplexCoord Nc) :
    T (cmp99FlatComplexFibrePointSource y v) =
      (((N : ℂ) ^ d)⁻¹) •
        ∑ k : FinBox d N,
          (cmp99FlatFourierMode k y)⁻¹ •
            T (cmp99FlatComplexFibreFourierMode k v) := by
  rw [cmp99FlatComplexFibrePointSource_eq_normalized_sum_fourierMode]
  simp only [map_smul, map_sum]

end

end YangMills.RG
