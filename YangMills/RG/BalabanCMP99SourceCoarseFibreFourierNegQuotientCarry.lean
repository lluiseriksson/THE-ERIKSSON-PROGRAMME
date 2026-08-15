/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCoarseFibreFourierNeg
import YangMills.RG.BalabanCMP99SourceFlatQprimeAliasFibreDictionary

/-!
# Euclidean quotient carry under cross-fibre Fourier negation

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations have not yet been compiler verified.

Periodic negation changes both the coarse residue and the Euclidean quotient
of a fine momentum.  This module exposes the exact natural-valued quotient
law before passing to the signed centered-alias dictionary: the target
quotient is `-q` when the coarse residue is zero and `-q-1` otherwise.

Honest scope: this is arithmetic on the two literal fine-momentum fibres.  It
does not identify the induced signed-alias map, an endpoint phase, a regional
`B0`, window 15, a terminal field or a `TermSource` inhabitant.
-/

namespace YangMills.RG

noncomputable section

/-- Canonical periodic negation at the level of natural representatives. -/
@[simp] theorem cmp99FinBoxFourierNeg_apply_val
    {d N : ℕ} [NeZero N] (k : FinBox d N) (mu : Fin d) :
    (cmp99FinBoxFourierNeg k mu).val =
      (N - (k mu).val) % N := by
  change (-((k mu).val : ZMod N)).val = _
  rw [ZMod.neg_val']
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (k mu).isLt]

/-- Pure Euclidean arithmetic behind the quotient carry. -/
private theorem periodicNegQuotient
    (M N ell q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hell : ell < N) (hq : q < M) :
    ((M * N - (ell + N * q)) % (M * N)) / N =
      if ell = 0 then (M - q) % M else M - q - 1 := by
  by_cases he : ell = 0
  · subst ell
    rw [if_pos rfl, zero_add]
    by_cases hq0 : q = 0
    · subst q
      simp
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      have hsublt : M - q < M := Nat.sub_lt hM hqpos
      have hnum : M * N - N * q = (M - q) * N := by
        rw [Nat.sub_mul]
        simp only [Nat.mul_comm]
      rw [hnum, Nat.mod_eq_of_lt ((Nat.mul_lt_mul_right hN).2 hsublt),
        Nat.mul_div_left _ hN, Nat.mod_eq_of_lt hsublt]
  · have hellpos : 0 < ell := Nat.pos_of_ne_zero he
    have hqle : q + 1 ≤ M := Nat.succ_le_iff.mpr hq
    have hsumlt : ell + N * q < M * N := by
      calc
        ell + N * q < N + N * q := Nat.add_lt_add_right hell _
        _ = N * (q + 1) := by ring
        _ ≤ N * M := Nat.mul_le_mul_left N hqle
        _ = M * N := Nat.mul_comm _ _
    have hnumlt : M * N - (ell + N * q) < M * N := by omega
    rw [if_neg he, Nat.mod_eq_of_lt hnumlt]
    have hsubpos : 0 < M - q := Nat.sub_pos_of_lt hq
    have hsubsucc : M - q = (M - q - 1) + 1 := by omega
    have hMNq : M * N - N * q = (M - q) * N := by
      rw [Nat.sub_mul]
      simp only [Nat.mul_comm]
    have hrewrite :
        M * N - (ell + N * q) =
          (N - ell) + N * (M - q - 1) := by
      calc
        M * N - (ell + N * q) = (M * N - N * q) - ell := by omega
        _ = (M - q) * N - ell := by rw [hMNq]
        _ = ((M - q - 1) + 1) * N - ell :=
          congrArg (fun t => t * N - ell) hsubsucc
        _ = ((M - q - 1) * N + N) - ell := by ring
        _ = (M - q - 1) * N + (N - ell) := by omega
        _ = (N - ell) + N * (M - q - 1) := by ac_rfl
    rw [hrewrite, Nat.add_mul_div_left (N - ell) (M - q - 1) hN]
    rw [Nat.div_eq_of_lt (by omega : N - ell < N)]
    omega

/-- The target Euclidean quotient under cross-fibre periodic negation.  The
outer `% M` in the zero-residue branch is essential at `q = 0`. -/
theorem cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv_quotient_val
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : {k : FinBox d (M * N') //
      cmp99SourceFlatQprimeCoarseAlias k = ell}) (mu : Fin d) :
    let q := cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N' ell k
    let k' := cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
      d M N' ell k
    let q' := cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N'
      (cmp99FinBoxFourierNeg ell) k'
    (q' mu).val =
      if (ell mu).val = 0 then (M - (q mu).val) % M
      else M - (q mu).val - 1 := by
  dsimp only
  change (cmp99FinBoxFourierNeg k.1 mu).val / N' =
    if (ell mu).val = 0 then
      (M - (k.1 mu).val / N') % M
    else M - (k.1 mu).val / N' - 1
  rw [cmp99FinBoxFourierNeg_apply_val]
  have hmod : (k.1 mu).val % N' = (ell mu).val := by
    exact congrArg Fin.val (congrFun k.property mu)
  have hk : (k.1 mu).val =
      (ell mu).val + N' * ((k.1 mu).val / N') := by
    calc
      (k.1 mu).val =
          (k.1 mu).val % N' + N' * ((k.1 mu).val / N') :=
        (Nat.mod_add_div _ _).symm
      _ = (ell mu).val + N' * ((k.1 mu).val / N') := by rw [hmod]
  conv_lhs => rw [hk]
  exact periodicNegQuotient M N' (ell mu).val
    ((k.1 mu).val / N') (Nat.pos_of_ne_zero (NeZero.ne M))
    (Nat.pos_of_ne_zero (NeZero.ne N')) (ell mu).isLt
    (k.1 mu).divNat.isLt

/-- Residue form consumed by the later signed-alias affine carry. -/
theorem cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv_quotient_cast
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : {k : FinBox d (M * N') //
      cmp99SourceFlatQprimeCoarseAlias k = ell}) (mu : Fin d) :
    let q := cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N' ell k
    let k' := cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
      d M N' ell k
    let q' := cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N'
      (cmp99FinBoxFourierNeg ell) k'
    ((q' mu).val : ZMod M) =
      -((q mu).val : ZMod M) -
        (if (ell mu).val = 0 then 0 else 1 : ZMod M) := by
  let q := cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N' ell k
  let k' := cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
    d M N' ell k
  let q' := cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N'
    (cmp99FinBoxFourierNeg ell) k'
  change ((q' mu).val : ZMod M) =
    -((q mu).val : ZMod M) -
      (if (ell mu).val = 0 then 0 else 1 : ZMod M)
  have hval : (q' mu).val =
      if (ell mu).val = 0 then (M - (q mu).val) % M
      else M - (q mu).val - 1 := by
    simpa only [q, k', q'] using
      (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv_quotient_val
        ell k mu)
  rw [hval]
  split_ifs with he
  · rw [ZMod.natCast_mod, Nat.cast_sub (Nat.le_of_lt (q mu).isLt)]
    simp
  · have hqsucc : (q mu).val + 1 ≤ M := Nat.succ_le_iff.mpr (q mu).isLt
    rw [show M - (q mu).val - 1 = M - ((q mu).val + 1) by omega,
      Nat.cast_sub hqsucc]
    push_cast
    rw [ZMod.natCast_self]
    ring

end

end YangMills.RG
