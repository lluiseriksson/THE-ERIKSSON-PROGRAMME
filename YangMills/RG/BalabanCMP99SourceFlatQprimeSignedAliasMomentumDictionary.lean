/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireAveragePeriodicity
import YangMills.RG.BalabanCMP99SourceFlatQprimeAliasFibreDictionary

/-!
# PRE-VALIDATION: signed flat Qprime momentum to the printed CMP89 alias fibre

The source is present, its `.olean` has not yet been materialized, and the
result has not yet been verified by the compiler.

The cold-sealed fibre dictionary enumerates a quotient coordinate `q : Fin M`
by the centered interval.  Enumeration alone does not identify physical
momenta: the exact one-block amplitude is evaluated at `-M * p_fine`, so the
printed reciprocal alias must represent `-q` modulo `M`.

This module constructs that signed representative through the affine
involution `x |-> -x - lower` on `ZMod M`.  It then proves that the exact
physical amplitude momentum and the printed CMP89 alias momentum differ only
by coordinatewise integer multiples of the genuine amplitude period
`2*pi*M`.  Column and opposite-momentum row transports are kept separate.

No orientation is inferred from the name "row", and the already sealed
order-preserving enumeration is not promoted to a momentum identity.  No
weighted adjoint, `Q'^* Q'`, precision, inverse or regional Green operator is
constructed here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The affine involution on residues which compensates for the lower endpoint
of the printed centered interval and reverses the physical momentum. -/
def cmp99SourceFlatQprimeSignedResidueAffineEquiv
    (M : ℕ) [NeZero M] : Equiv.Perm (ZMod M) where
  toFun x := -x - (cmp89Eq245CenteredAliasLower M : ZMod M)
  invFun x := -x - (cmp89Eq245CenteredAliasLower M : ZMod M)
  left_inv x := by simp
  right_inv x := by simp

/-- The quotient residue is first reflected in `ZMod M`, then returned to its
canonical nonnegative representative. -/
def cmp99SourceFlatQprimeSignedResidueEquiv
    (M : ℕ) [NeZero M] : Equiv.Perm (Fin M) :=
  (ZMod.finEquiv M).toEquiv |>.trans
    ((cmp99SourceFlatQprimeSignedResidueAffineEquiv M).trans
      (ZMod.finEquiv M).symm.toEquiv)

/-- Canonical centered representative of the physical residue `-q mod M`.
The lower-endpoint correction is part of the equivalence, not an assumed
periodicity convention. -/
def cmp99SourceFlatQprimeSignedCenteredAliasEquiv
    (M : ℕ) [NeZero M] :
    Fin M ≃ {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers M} :=
  (cmp99SourceFlatQprimeSignedResidueEquiv M).trans
    (cmp99SourceFlatQprimeCenteredAliasEquiv M)

/-- The signed centered representative is congruent to the negative quotient
residue. -/
theorem cmp99SourceFlatQprimeSignedCenteredAliasEquiv_cast_eq_neg
    (M : ℕ) [NeZero M] (q : Fin M) :
    (((cmp99SourceFlatQprimeSignedCenteredAliasEquiv M q).1 : ℤ) : ZMod M) =
      -((q.1 : ℕ) : ZMod M) := by
  change
    (((cmp89Eq245CenteredAliasLower M +
        ((cmp99SourceFlatQprimeSignedResidueEquiv M q).1 : ℕ) : ℤ)) :
      ZMod M) = -((q.1 : ℕ) : ZMod M)
  simp only [Int.cast_add, Int.cast_natCast]
  change
    (cmp89Eq245CenteredAliasLower M : ZMod M) +
        ZMod.finEquiv M (cmp99SourceFlatQprimeSignedResidueEquiv M q) =
      -ZMod.finEquiv M q
  simp [cmp99SourceFlatQprimeSignedResidueEquiv,
    cmp99SourceFlatQprimeSignedResidueAffineEquiv]

/-- Equivalently, the alias integer plus the nonnegative quotient is an exact
integer multiple of the reciprocal period count `M`. -/
theorem cmp99SourceFlatQprimeSignedCenteredAlias_add_quotient_dvd
    (M : ℕ) [NeZero M] (q : Fin M) :
    (M : ℤ) ∣
      (cmp99SourceFlatQprimeSignedCenteredAliasEquiv M q).1 + (q.1 : ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [cmp99SourceFlatQprimeSignedCenteredAliasEquiv_cast_eq_neg]
  ring

/-- Source-faithful signed dictionary from a fixed coarse fine-momentum fibre
to the printed centered CMP89 alias fibre. -/
def cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
    (d M N' : ℕ) [NeZero M] [NeZero N']
    (ell : FinBox d N') :
    {k : FinBox d (M * N') // cmp99SourceFlatQprimeCoarseAlias k = ell} ≃
      CMP89Eq246AliasIndex d M 1 := by
  let e :
      {k : FinBox d (M * N') // cmp99SourceFlatQprimeCoarseAlias k = ell} ≃
        {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d M} :=
    (cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N' ell).trans
      ((Equiv.piCongrRight fun _ : Fin d =>
          cmp99SourceFlatQprimeSignedCenteredAliasEquiv M).trans
        (cmp89Eq245CenteredAliasVectorPiEquiv d M).symm)
  simpa only [CMP89Eq246AliasIndex, pow_one] using e

/-- The coarse complex momentum paired with the signed reciprocal alias. -/
def cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') : Fin d → ℂ :=
  fun mu => -((2 * Real.pi : ℂ) * (ell mu).val / (N' : ℂ))

/-- Any vector of integer multiples of the exact `2*pi*M` period leaves the
entire averaging amplitude unchanged. -/
theorem cmp89Eq245EntireAverageAmplitude_add_int_aliasPeriods
    {d M : ℕ} (hM : 0 < M) (z : Fin d → ℂ) (w : Fin d → ℤ) :
    cmp89Eq245EntireAverageAmplitude d M
        (fun mu => z mu + (w mu : ℂ) *
          (((2 * Real.pi * (M : ℝ) : ℝ) : ℂ))) =
      cmp89Eq245EntireAverageAmplitude d M z := by
  unfold cmp89Eq245EntireAverageAmplitude
  apply Finset.prod_congr rfl
  intro mu _
  exact cmp89Eq245EntireAverageFactor_add_int_aliasPeriod
    hM (w mu) (z mu)

/-- The physical signed amplitude momentum equals the printed alias momentum
up to an internally constructed integer multiple of `2*pi*M` in every
coordinate. -/
theorem cmp99SourceFlatQprimeAmplitudeMomentum_eq_alias_add_period
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : {k : FinBox d (M * N') //
      cmp99SourceFlatQprimeCoarseAlias k = ell}) :
    ∃ w : Fin d → ℤ,
      cmp99SourceFlatQprimeAmplitudeMomentum k.1 =
        fun mu =>
          cmp89Eq248EntireAliasMomentum
              (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
              (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
                d M N' ell k).1 mu +
            (w mu : ℂ) * (((2 * Real.pi * (M : ℝ) : ℝ) : ℂ)) := by
  let q := cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N' ell k
  let m := cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
    d M N' ell k
  have hm : ∀ mu : Fin d,
      (M : ℤ) ∣ m.1 mu + (q mu).val := by
    intro mu
    change (M : ℤ) ∣
      (cmp99SourceFlatQprimeSignedCenteredAliasEquiv M (q mu)).1 +
        ((q mu).val : ℤ)
    exact cmp99SourceFlatQprimeSignedCenteredAlias_add_quotient_dvd M (q mu)
  choose c hc using hm
  refine ⟨fun mu => -c mu, ?_⟩
  funext mu
  have hk : (k.1 mu).val = (ell mu).val + N' * (q mu).val := by
    simpa [q] using
      (cmp99SourceFlatQprimeFixedCoarseFibreEquiv_symm_apply_val
        d M N' ell q mu)
  have hkC := congrArg (fun x : ℕ => (x : ℂ)) hk
  have hcC := congrArg (fun x : ℤ => (x : ℂ)) (hc mu)
  push_cast at hkC hcC
  have hM : (M : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  have hN : (N' : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N')
  simp only [cmp99SourceFlatQprimeAmplitudeMomentum,
    cmp99FlatDiscreteMomentum,
    cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum,
    cmp89Eq248EntireAliasMomentum, cmp89Eq245AliasShift]
  push_cast
  field_simp [hM, hN]
  linear_combination
    -(2 * (Real.pi : ℂ) * M) * hkC +
      (2 * (Real.pi : ℂ) * N') * hcC

/-- Exact transport of the physical one-block column amplitude to the printed
CMP89 alias column. -/
theorem cmp99SourceFlatQprimeAmplitude_eq_entireAliasColumn
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : {k : FinBox d (M * N') //
      cmp99SourceFlatQprimeCoarseAlias k = ell}) :
    cmp89Eq245EntireAverageAmplitude d M
        (cmp99SourceFlatQprimeAmplitudeMomentum k.1) =
      cmp89Eq246EntireAliasAverageColumn d M 1
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell k) := by
  rcases cmp99SourceFlatQprimeAmplitudeMomentum_eq_alias_add_period ell k with
    ⟨w, hw⟩
  rw [hw]
  simpa [cmp89Eq246EntireAliasAverageColumn, pow_one] using
    cmp89Eq245EntireAverageAmplitude_add_int_aliasPeriods
      (Nat.pos_of_ne_zero (NeZero.ne M))
      (cmp89Eq248EntireAliasMomentum
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell k).1) w

/-- Exact transport of the opposite physical amplitude to the separate
holomorphic CMP89 row factor. -/
theorem cmp99SourceFlatQprimeNegAmplitude_eq_entireAliasRow
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : {k : FinBox d (M * N') //
      cmp99SourceFlatQprimeCoarseAlias k = ell}) :
    cmp89Eq245EntireAverageAmplitude d M
        (-cmp99SourceFlatQprimeAmplitudeMomentum k.1) =
      cmp89Eq246EntireAliasAverageRow d M 1
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell k) := by
  rcases cmp99SourceFlatQprimeAmplitudeMomentum_eq_alias_add_period ell k with
    ⟨w, hw⟩
  have hneg :
      -cmp99SourceFlatQprimeAmplitudeMomentum k.1 =
        fun mu =>
          -cmp89Eq248EntireAliasMomentum
              (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
              (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
                d M N' ell k).1 mu +
            ((-w mu : ℤ) : ℂ) *
              (((2 * Real.pi * (M : ℝ) : ℝ) : ℂ)) := by
    funext mu
    rw [congrFun hw mu]
    push_cast
    ring
  rw [hneg]
  simpa [cmp89Eq246EntireAliasAverageRow, pow_one] using
    cmp89Eq245EntireAverageAmplitude_add_int_aliasPeriods
      (Nat.pos_of_ne_zero (NeZero.ne M))
      (-cmp89Eq248EntireAliasMomentum
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell k).1) (fun mu => -w mu)

end

end YangMills.RG
