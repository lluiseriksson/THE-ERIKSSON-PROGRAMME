/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Fourier.ZMod
import YangMills.RG.BalabanCMP99SourceFlatFourierStencil

/-!
# PRE-VALIDATION: multidimensional flat discrete Fourier convention

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

`ZMod.dft` fixes the one-dimensional convention: the forward transform uses
the negative standard character and the inverse uses the positive character
with one factor `N^-1`.  This module takes the product of that convention over
`Fin d`, proves the exact product-character orthogonality relation and bundles
the resulting transform as a complex-linear equivalence.

Honest scope: this is the full periodic scalar transform on
`Fin d -> ZMod N`.  The adapters to `FinBox`, active-region restrictions and
the `SUNLieComplexCoord` fibre are separate obligations.  No regional or
interacting Fourier diagonalization is asserted here.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Additive periodic momentum/site box used by the product DFT. -/
abbrev CMP99FlatZModBox (d N : ℕ) := Fin d → ZMod N

/-- Positive product character.  Its two arguments are kept in this order so
the sign convention of the forward transform remains visible. -/
def cmp99FlatZModFourierCharacter {d N : ℕ}
    (k x : CMP99FlatZModBox d N) : ℂ :=
  ∏ mu, ZMod.stdAddChar (k mu * x mu)

theorem cmp99FlatZModFourierCharacter_comm {d N : ℕ}
    (k x : CMP99FlatZModBox d N) :
    cmp99FlatZModFourierCharacter k x =
      cmp99FlatZModFourierCharacter x k := by
  unfold cmp99FlatZModFourierCharacter
  apply Finset.prod_congr rfl
  intro mu _
  rw [mul_comm]

theorem cmp99FlatZModFourierCharacter_add_left {d N : ℕ}
    (k l x : CMP99FlatZModBox d N) :
    cmp99FlatZModFourierCharacter (k + l) x =
      cmp99FlatZModFourierCharacter k x *
        cmp99FlatZModFourierCharacter l x := by
  unfold cmp99FlatZModFourierCharacter
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro mu _
  rw [Pi.add_apply, add_mul, AddChar.map_add_eq_mul]

theorem cmp99FlatZModFourierCharacter_add_right {d N : ℕ}
    (k x y : CMP99FlatZModBox d N) :
    cmp99FlatZModFourierCharacter k (x + y) =
      cmp99FlatZModFourierCharacter k x *
        cmp99FlatZModFourierCharacter k y := by
  rw [cmp99FlatZModFourierCharacter_comm,
    cmp99FlatZModFourierCharacter_add_left]
  congr 1 <;> rw [cmp99FlatZModFourierCharacter_comm]

theorem cmp99FlatZModFourierCharacter_neg_left {d N : ℕ}
    (k x : CMP99FlatZModBox d N) :
    cmp99FlatZModFourierCharacter (-k) x =
      (cmp99FlatZModFourierCharacter k x)⁻¹ := by
  unfold cmp99FlatZModFourierCharacter
  rw [map_neg, Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro mu _
  rw [Pi.neg_apply, neg_mul, map_neg]

theorem cmp99FlatZModFourierCharacter_neg_swap {d N : ℕ}
    (k x : CMP99FlatZModBox d N) :
    cmp99FlatZModFourierCharacter (-k) x =
      cmp99FlatZModFourierCharacter (-x) k := by
  unfold cmp99FlatZModFourierCharacter
  apply Finset.prod_congr rfl
  intro mu _
  rw [Pi.neg_apply, Pi.neg_apply]
  congr 1
  ring

/-- One-coordinate orthogonality for the exact standard character. -/
theorem sum_cmp99FlatZMod_standardCharacter_mul
    {N : ℕ} [NeZero N] (t : ZMod N) :
    (∑ a : ZMod N, ZMod.stdAddChar (a * t)) =
      if t = 0 then (N : ℂ) else 0 := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [if_neg ht]
    simpa only [mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ht))

/-- Product orthogonality over all `d` momentum coordinates. -/
theorem sum_cmp99FlatZModFourierCharacter
    {d N : ℕ} [NeZero N] (x : CMP99FlatZModBox d N) :
    (∑ k : CMP99FlatZModBox d N,
        cmp99FlatZModFourierCharacter k x) =
      if x = 0 then (N : ℂ) ^ d else 0 := by
  have hfactor :
      (∑ k : CMP99FlatZModBox d N,
          ∏ mu, ZMod.stdAddChar (k mu * x mu)) =
        ∏ mu, ∑ a : ZMod N, ZMod.stdAddChar (a * x mu) := by
    rw [← Fintype.piFinset_univ]
    simpa only using
      (Finset.sum_prod_piFinset
        (R := ℂ) (ι := Fin d) (Finset.univ : Finset (ZMod N))
        (fun mu a => ZMod.stdAddChar (a * x mu)))
  unfold cmp99FlatZModFourierCharacter
  rw [hfactor]
  by_cases hx : x = 0
  · subst x
    simp [sum_cmp99FlatZMod_standardCharacter_mul]
  · rw [if_neg hx]
    have hex : ∃ mu, x mu ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext fun mu => h mu)
    rcases hex with ⟨mu, hmu⟩
    apply Finset.prod_eq_zero (Finset.mem_univ mu)
    rw [sum_cmp99FlatZMod_standardCharacter_mul, if_neg hmu]

/-- Orthogonality kernel in the orientation used by forward analysis followed
by positive-character synthesis. -/
theorem sum_cmp99FlatZModFourierCharacter_mul_neg
    {d N : ℕ} [NeZero N] (x y : CMP99FlatZModBox d N) :
    (∑ k : CMP99FlatZModBox d N,
        cmp99FlatZModFourierCharacter k x *
          cmp99FlatZModFourierCharacter (-k) y) =
      if x = y then (N : ℂ) ^ d else 0 := by
  have hterm : ∀ k : CMP99FlatZModBox d N,
      cmp99FlatZModFourierCharacter k x *
          cmp99FlatZModFourierCharacter (-k) y =
        cmp99FlatZModFourierCharacter k (x - y) := by
    intro k
    rw [show -k = (-1 : ℤ) • k by simp]
    unfold cmp99FlatZModFourierCharacter
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro mu _
    rw [Pi.smul_apply, Pi.sub_apply]
    simp only [Int.reduceNeg, neg_smul, one_smul]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hterm]
  rw [sum_cmp99FlatZModFourierCharacter]
  simp only [sub_eq_zero]

/-- Unnormalized forward transform: negative character, exactly as in
`ZMod.dft`. -/
def cmp99FlatZModDFT {d N : ℕ}
    (phi : CMP99FlatZModBox d N → ℂ) (k : CMP99FlatZModBox d N) : ℂ :=
  ∑ x, cmp99FlatZModFourierCharacter (-k) x * phi x

/-- Inverse transform: positive character and the product normalization
`N^-d`. -/
def cmp99FlatZModInvDFT {d N : ℕ}
    (psi : CMP99FlatZModBox d N → ℂ) (x : CMP99FlatZModBox d N) : ℂ :=
  ((N : ℂ) ^ d)⁻¹ *
    ∑ k, cmp99FlatZModFourierCharacter k x * psi k

theorem cmp99FlatZModInvDFT_DFT {d N : ℕ} [NeZero N]
    (phi : CMP99FlatZModBox d N → ℂ) :
    cmp99FlatZModInvDFT (cmp99FlatZModDFT phi) = phi := by
  funext x
  unfold cmp99FlatZModInvDFT cmp99FlatZModDFT
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring
  rw [sum_cmp99FlatZModFourierCharacter_mul_neg]
  have hcard : (N : ℂ) ^ d ≠ 0 := by
    exact pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne N))
  simp [hcard]

theorem cmp99FlatZModDFT_InvDFT {d N : ℕ} [NeZero N]
    (psi : CMP99FlatZModBox d N → ℂ) :
    cmp99FlatZModDFT (cmp99FlatZModInvDFT psi) = psi := by
  funext k
  unfold cmp99FlatZModDFT cmp99FlatZModInvDFT
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_mul]
  apply congrArg (fun z : ℂ => z * psi l)
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm, cmp99FlatZModFourierCharacter_comm,
    cmp99FlatZModFourierCharacter_neg_swap,
    cmp99FlatZModFourierCharacter_comm]
  rw [sum_cmp99FlatZModFourierCharacter_mul_neg]
  have hcard : (N : ℂ) ^ d ≠ 0 := by
    exact pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne N))
  simp [hcard]

/-- The exact multidimensional DFT convention as a complex-linear
equivalence. -/
noncomputable def cmp99FlatZModDFTLinearEquiv {d N : ℕ} [NeZero N] :
    (CMP99FlatZModBox d N → ℂ) ≃ₗ[ℂ]
      (CMP99FlatZModBox d N → ℂ) where
  toFun := cmp99FlatZModDFT
  invFun := cmp99FlatZModInvDFT
  left_inv := cmp99FlatZModInvDFT_DFT
  right_inv := cmp99FlatZModDFT_InvDFT
  map_add' phi psi := by
    funext k
    unfold cmp99FlatZModDFT
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c phi := by
    funext k
    unfold cmp99FlatZModDFT
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

end

end YangMills.RG
