/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FlatFinBoxDFT
import YangMills.RG.BalabanCMP99PhysicalFibreComplexification
import YangMills.RG.BalabanCMP99SourceFlatQprimeCoarseAlias

/-!
# PRE-VALIDATION: physical-fibre DFT on the full flat periodic box

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

The exact scalar `FinBox` DFT is applied coordinatewise to the literal
complexified Lie fibre `SUNLieComplexCoord`.  Both inverse laws are proved
internally and bundled as a complex-linear equivalence.  The existing
physical Fourier mode is identified with the sealed product character, so
its forward transform is the exact single-momentum column with coefficient
`(N : ℂ)^d`.

Honest scope: this remains the full periodic box.  No active-region
restriction, source weighted-adjoint column, interacting transport, inverse
uniqueness or regional Green dictionary is asserted here.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

/-- The physical flat Fourier mode is literally the transported product
character fixed by the scalar DFT convention. -/
theorem cmp99FlatFourierMode_eq_finBoxFourierCharacter
    {d N : ℕ} [NeZero N] (k x : FinBox d N) :
    cmp99FlatFourierMode k x =
      cmp99FlatZModFourierCharacter
        (cmp99FinBoxZModEquiv d N k) (cmp99FinBoxZModEquiv d N x) := by
  rw [cmp99FlatFourierMode_eq_coordinateProduct]
  rfl

/-- The unnormalized negative-character DFT sends one positive product
character to the exact delta column. -/
theorem cmp99FlatZModDFT_fourierCharacter
    {d N : ℕ} [NeZero N]
    (l k : CMP99FlatZModBox d N) :
    cmp99FlatZModDFT (cmp99FlatZModFourierCharacter l) k =
      if l = k then (N : ℂ) ^ d else 0 := by
  unfold cmp99FlatZModDFT
  calc
    (∑ x, cmp99FlatZModFourierCharacter (-k) x *
        cmp99FlatZModFourierCharacter l x) =
        ∑ x, cmp99FlatZModFourierCharacter x l *
          cmp99FlatZModFourierCharacter (-x) k := by
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_comm, cmp99FlatZModFourierCharacter_comm l x,
        cmp99FlatZModFourierCharacter_neg_swap k x]
    _ = if l = k then (N : ℂ) ^ d else 0 := by
      rw [sum_cmp99FlatZModFourierCharacter_mul_neg]

/-- The literal `FinBox` DFT of the source Fourier mode is the exact delta
column, with no sign or normalization supplied by a caller. -/
theorem cmp99FlatFinBoxDFT_fourierMode
    {d N : ℕ} [NeZero N] (l k : FinBox d N) :
    cmp99FlatFinBoxDFT (cmp99FlatFourierMode l) k =
      if l = k then (N : ℂ) ^ d else 0 := by
  unfold cmp99FlatFinBoxDFT
  have hfun :
      (fun x => cmp99FlatFourierMode l
          ((cmp99FinBoxZModEquiv d N).symm x)) =
        cmp99FlatZModFourierCharacter (cmp99FinBoxZModEquiv d N l) := by
    funext x
    rw [cmp99FlatFourierMode_eq_finBoxFourierCharacter]
    simp only [Equiv.apply_symm_apply]
  rw [hfun, cmp99FlatZModDFT_fourierCharacter]
  by_cases h : l = k
  · subst k
    simp
  · rw [if_neg h, if_neg]
    intro heq
    exact h ((cmp99FinBoxZModEquiv d N).injective heq)

/-- A scalar factor independent of the site exits the exact `FinBox` DFT on
the right. -/
theorem cmp99FlatFinBoxDFT_mul_const
    {d N : ℕ} [NeZero N]
    (phi : FinBox d N → ℂ) (c : ℂ) (k : FinBox d N) :
    cmp99FlatFinBoxDFT (fun x => phi x * c) k =
      cmp99FlatFinBoxDFT phi k * c := by
  unfold cmp99FlatFinBoxDFT cmp99FlatZModDFT
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Coordinatewise forward DFT on the literal complexified physical Lie
fibre. -/
def cmp99FlatPhysicalFibreDFT
    {d N Nc : ℕ} [NeZero N]
    (phi : FinBox d N → SUNLieComplexCoord Nc)
    (k : FinBox d N) : SUNLieComplexCoord Nc :=
  WithLp.toLp 2 fun a =>
    cmp99FlatFinBoxDFT (fun x => phi x a) k

/-- Coordinatewise inverse DFT on the literal complexified physical Lie
fibre. -/
def cmp99FlatPhysicalFibreInvDFT
    {d N Nc : ℕ} [NeZero N]
    (psi : FinBox d N → SUNLieComplexCoord Nc)
    (x : FinBox d N) : SUNLieComplexCoord Nc :=
  WithLp.toLp 2 fun a =>
    cmp99FlatFinBoxInvDFT (fun k => psi k a) x

@[simp] theorem cmp99FlatPhysicalFibreDFT_apply
    {d N Nc : ℕ} [NeZero N]
    (phi : FinBox d N → SUNLieComplexCoord Nc)
    (k : FinBox d N) (a : Fin (Nc ^ 2 - 1)) :
    cmp99FlatPhysicalFibreDFT phi k a =
      cmp99FlatFinBoxDFT (fun x => phi x a) k := rfl

@[simp] theorem cmp99FlatPhysicalFibreInvDFT_apply
    {d N Nc : ℕ} [NeZero N]
    (psi : FinBox d N → SUNLieComplexCoord Nc)
    (x : FinBox d N) (a : Fin (Nc ^ 2 - 1)) :
    cmp99FlatPhysicalFibreInvDFT psi x a =
      cmp99FlatFinBoxInvDFT (fun k => psi k a) x := rfl

theorem cmp99FlatPhysicalFibreInvDFT_DFT
    {d N Nc : ℕ} [NeZero N]
    (phi : FinBox d N → SUNLieComplexCoord Nc) :
    cmp99FlatPhysicalFibreInvDFT (cmp99FlatPhysicalFibreDFT phi) = phi := by
  funext x
  ext a
  change cmp99FlatFinBoxInvDFT
      (fun k => cmp99FlatFinBoxDFT (fun y => phi y a) k) x = phi x a
  exact congrFun (cmp99FlatFinBoxInvDFT_DFT (fun y => phi y a)) x

theorem cmp99FlatPhysicalFibreDFT_InvDFT
    {d N Nc : ℕ} [NeZero N]
    (psi : FinBox d N → SUNLieComplexCoord Nc) :
    cmp99FlatPhysicalFibreDFT (cmp99FlatPhysicalFibreInvDFT psi) = psi := by
  funext k
  ext a
  change cmp99FlatFinBoxDFT
      (fun x => cmp99FlatFinBoxInvDFT (fun l => psi l a) x) k = psi k a
  exact congrFun (cmp99FlatFinBoxDFT_InvDFT (fun l => psi l a)) k

/-- The exact full-box physical-fibre DFT as a complex-linear equivalence. -/
noncomputable def cmp99FlatPhysicalFibreDFTLinearEquiv
    {d N Nc : ℕ} [NeZero N] :
    (FinBox d N → SUNLieComplexCoord Nc) ≃ₗ[ℂ]
      (FinBox d N → SUNLieComplexCoord Nc) where
  toFun := cmp99FlatPhysicalFibreDFT
  invFun := cmp99FlatPhysicalFibreInvDFT
  left_inv := cmp99FlatPhysicalFibreInvDFT_DFT
  right_inv := cmp99FlatPhysicalFibreDFT_InvDFT
  map_add' phi psi := by
    funext k
    ext a
    change cmp99FlatFinBoxDFT (fun x => phi x a + psi x a) k =
      cmp99FlatFinBoxDFT (fun x => phi x a) k +
        cmp99FlatFinBoxDFT (fun x => psi x a) k
    exact congrFun
      ((cmp99FlatFinBoxDFTLinearEquiv).map_add
        (fun x => phi x a) (fun x => psi x a)) k
  map_smul' c phi := by
    funext k
    ext a
    change cmp99FlatFinBoxDFT (fun x => c * phi x a) k =
      c * cmp99FlatFinBoxDFT (fun x => phi x a) k
    simpa only [smul_eq_mul] using congrFun
      ((cmp99FlatFinBoxDFTLinearEquiv).map_smul c (fun x => phi x a)) k

/-- Exact physical-fibre delta column of one source Fourier mode. -/
theorem cmp99FlatPhysicalFibreDFT_fourierMode
    {d N Nc : ℕ} [NeZero N]
    (l k : FinBox d N) (v : SUNLieComplexCoord Nc) :
    cmp99FlatPhysicalFibreDFT
        (cmp99FlatComplexFibreFourierMode l v) k =
      (if l = k then (N : ℂ) ^ d else 0) • v := by
  ext a
  change cmp99FlatFinBoxDFT
      (fun x => cmp99FlatFourierMode l x * v a) k =
    (if l = k then (N : ℂ) ^ d else 0) * v a
  rw [cmp99FlatFinBoxDFT_mul_const, cmp99FlatFinBoxDFT_fourierMode]

end

end YangMills.RG
