/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FlatMultidimensionalDFT

/-!
# PRE-VALIDATION: exact FinBox transport of the flat DFT

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

The scalar product DFT is already fixed on `Fin d → ZMod N`.  This module
constructs the literal coordinate equivalence with `FinBox d N`, transports
both transforms through it, and proves both inverse laws.  The normalization
and character signs therefore remain those of the sealed product DFT; they
are not restated as caller data.

Honest scope: this is still the full scalar periodic box.  Active-region
restriction, the `SUNLieComplexCoord` fibre, the direct Fourier column and
the interacting/regional inverse dictionaries remain separate obligations.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- Literal coordinate dictionary from the concrete periodic box to the
additive `ZMod` box used by the product DFT. -/
def cmp99FinBoxZModEquiv (d N : ℕ) [NeZero N] :
    FinBox d N ≃ CMP99FlatZModBox d N where
  toFun x mu := ((x mu).val : ZMod N)
  invFun z mu := ⟨(z mu).val, (z mu).val_lt⟩
  left_inv x := by
    funext mu
    apply Fin.ext
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt (x mu).isLt]
  right_inv z := by
    funext mu
    exact ZMod.natCast_zmod_val (z mu)

@[simp] theorem cmp99FinBoxZModEquiv_apply
    {d N : ℕ} [NeZero N] (x : FinBox d N) (mu : Fin d) :
    cmp99FinBoxZModEquiv d N x mu = ((x mu).val : ZMod N) := rfl

@[simp] theorem cmp99FinBoxZModEquiv_symm_apply_val
    {d N : ℕ} [NeZero N] (z : CMP99FlatZModBox d N) (mu : Fin d) :
    ((cmp99FinBoxZModEquiv d N).symm z mu).val = (z mu).val := rfl

/-- Forward DFT on the literal `FinBox`, obtained only by transporting the
sealed negative-character product transform. -/
def cmp99FlatFinBoxDFT {d N : ℕ} [NeZero N]
    (phi : FinBox d N → ℂ) (k : FinBox d N) : ℂ :=
  cmp99FlatZModDFT
    (fun x => phi ((cmp99FinBoxZModEquiv d N).symm x))
    (cmp99FinBoxZModEquiv d N k)

/-- Inverse DFT on the literal `FinBox`, with the sealed positive character
and literal normalization `((N : ℂ)^d)⁻¹`. -/
def cmp99FlatFinBoxInvDFT {d N : ℕ} [NeZero N]
    (psi : FinBox d N → ℂ) (x : FinBox d N) : ℂ :=
  cmp99FlatZModInvDFT
    (fun k => psi ((cmp99FinBoxZModEquiv d N).symm k))
    (cmp99FinBoxZModEquiv d N x)

theorem cmp99FlatFinBoxInvDFT_DFT {d N : ℕ} [NeZero N]
    (phi : FinBox d N → ℂ) :
    cmp99FlatFinBoxInvDFT (cmp99FlatFinBoxDFT phi) = phi := by
  funext x
  have h := congrFun
    (cmp99FlatZModInvDFT_DFT
      (fun z => phi ((cmp99FinBoxZModEquiv d N).symm z)))
    (cmp99FinBoxZModEquiv d N x)
  simpa only [cmp99FlatFinBoxInvDFT, cmp99FlatFinBoxDFT,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply] using h

theorem cmp99FlatFinBoxDFT_InvDFT {d N : ℕ} [NeZero N]
    (psi : FinBox d N → ℂ) :
    cmp99FlatFinBoxDFT (cmp99FlatFinBoxInvDFT psi) = psi := by
  funext k
  have h := congrFun
    (cmp99FlatZModDFT_InvDFT
      (fun z => psi ((cmp99FinBoxZModEquiv d N).symm z)))
    (cmp99FinBoxZModEquiv d N k)
  simpa only [cmp99FlatFinBoxInvDFT, cmp99FlatFinBoxDFT,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply] using h

/-- The exact scalar `FinBox` DFT as a complex-linear equivalence. -/
noncomputable def cmp99FlatFinBoxDFTLinearEquiv {d N : ℕ} [NeZero N] :
    (FinBox d N → ℂ) ≃ₗ[ℂ] (FinBox d N → ℂ) where
  toFun := cmp99FlatFinBoxDFT
  invFun := cmp99FlatFinBoxInvDFT
  left_inv := cmp99FlatFinBoxInvDFT_DFT
  right_inv := cmp99FlatFinBoxDFT_InvDFT
  map_add' phi psi := by
    funext k
    unfold cmp99FlatFinBoxDFT cmp99FlatZModDFT
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c phi := by
    funext k
    unfold cmp99FlatFinBoxDFT cmp99FlatZModDFT
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [RingHom.id_apply]
    ring

end

end YangMills.RG
