/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Fourier.ZMod
import YangMills.RG.BalabanCMP99SourceFlatAmbientLaplacian

/-!
# PRE-VALIDATION: Fourier modes of the flat periodic CMP99 stencil

Source is present, the corresponding `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

This module diagonalizes the scalar complex stencil that is definitionally
parallel to `cmp99FlatPeriodicLaplacianStencil`.  The phase is built from the
literal `FinBox d N -> ZMod N` coordinate dictionary and Mathlib's standard
additive character, so the orientation and normalization are visible.

Honest scope: the physical CMP99 zero-cochain has the real fibre
`SUNLieCoord Nc`.  No complexification of that fibre is constructed here.
Consequently this is the scalar Fourier brick needed by the operator
dictionary, not yet a diagonalization theorem for the physical operator,
the `Q'` term, the Green inverse, or its regional compression.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d N : ℕ} [NeZero N]

/-- Casting a reduced natural coordinate into `ZMod` removes the explicit
remainder.  Kept local to the Fourier dictionary so it does not import the
much larger concrete-RG fidelity lane. -/
private lemma cmp99Flat_natCast_mod_zmod (a n : ℕ) :
    ((a % n : ℕ) : ZMod n) = (a : ZMod n) := by
  conv_rhs => rw [← Nat.div_add_mod a n]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- A positive periodic shift adds one to exactly its shifted `ZMod`
coordinate. -/
private lemma cmp99Flat_shift_val_zmod
    (x : FinBox d N) (i μ : Fin d) :
    (((x.shift i) μ).val : ZMod N) =
      ((x μ).val : ZMod N) + if μ = i then 1 else 0 := by
  by_cases h : μ = i
  · subst μ
    have hv : ((x.shift i) i).val = ((x i).val + 1) % N := by
      simp [FinBox.shift]
    rw [hv, if_pos rfl, cmp99Flat_natCast_mod_zmod]
    push_cast
    ring
  · have hv : (x.shift i) μ = x μ := by simp [FinBox.shift, h]
    rw [hv, if_neg h, add_zero]

/-- The positive-orientation `ZMod` phase pairing on the periodic box. -/
def cmp99FlatFourierPhase (k x : FinBox d N) : ZMod N :=
  ∑ μ : Fin d, ((k μ).val : ZMod N) * ((x μ).val : ZMod N)

/-- A positive shift adds the corresponding momentum coordinate to the
phase. -/
theorem cmp99FlatFourierPhase_shift
    (k x : FinBox d N) (i : Fin d) :
    cmp99FlatFourierPhase k (x.shift i) =
      cmp99FlatFourierPhase k x + ((k i).val : ZMod N) := by
  unfold cmp99FlatFourierPhase
  calc
    ∑ μ : Fin d, ((k μ).val : ZMod N) * (((x.shift i) μ).val : ZMod N) =
        ∑ μ : Fin d, (((k μ).val : ZMod N) * ((x μ).val : ZMod N) +
          if μ = i then ((k μ).val : ZMod N) else 0) := by
            apply Finset.sum_congr rfl
            intro μ _
            rw [cmp99Flat_shift_val_zmod]
            by_cases h : μ = i
            · simp [h]
              ring
            · simp [h]
    _ = (∑ μ : Fin d, ((k μ).val : ZMod N) * ((x μ).val : ZMod N)) +
          ∑ μ : Fin d, if μ = i then ((k μ).val : ZMod N) else 0 := by
            rw [Finset.sum_add_distrib]
    _ = (∑ μ : Fin d, ((k μ).val : ZMod N) * ((x μ).val : ZMod N)) +
          ((k i).val : ZMod N) := by simp

/-- A negative periodic shift subtracts the corresponding momentum
coordinate from the phase. -/
theorem cmp99FlatFourierPhase_shiftBack
    (k x : FinBox d N) (i : Fin d) :
    cmp99FlatFourierPhase k (x.shiftBack i) =
      cmp99FlatFourierPhase k x - ((k i).val : ZMod N) := by
  have h := cmp99FlatFourierPhase_shift k (x.shiftBack i) i
  rw [FinBox.shift_shiftBack] at h
  exact eq_sub_of_add_eq h.symm

/-- Positive-orientation Fourier character on the literal periodic box. -/
def cmp99FlatFourierMode (k x : FinBox d N) : ℂ :=
  ZMod.stdAddChar (cmp99FlatFourierPhase k x)

/-- A positive lattice shift multiplies the mode by the positive standard
character of the shifted momentum coordinate. -/
theorem cmp99FlatFourierMode_shift
    (k x : FinBox d N) (i : Fin d) :
    cmp99FlatFourierMode k (x.shift i) =
      ZMod.stdAddChar ((k i).val : ZMod N) * cmp99FlatFourierMode k x := by
  unfold cmp99FlatFourierMode
  rw [cmp99FlatFourierPhase_shift, AddChar.map_add_eq_mul]
  ring

/-- A negative lattice shift multiplies the mode by the inverse character. -/
theorem cmp99FlatFourierMode_shiftBack
    (k x : FinBox d N) (i : Fin d) :
    cmp99FlatFourierMode k (x.shiftBack i) =
      ZMod.stdAddChar (-((k i).val : ZMod N)) * cmp99FlatFourierMode k x := by
  unfold cmp99FlatFourierMode
  rw [cmp99FlatFourierPhase_shiftBack, sub_eq_add_neg,
    AddChar.map_add_eq_mul]
  ring

/-- Scalar complex counterpart of the sealed flat physical stencil. -/
def cmp99FlatPeriodicComplexStencil
    (phi : FinBox d N → ℂ) (x : FinBox d N) : ℂ :=
  ∑ i : Fin d,
    ((phi x - phi (x.shift i)) - (phi (x.shiftBack i) - phi x))

/-- Literal eigenvalue of the symmetric periodic nearest-neighbour stencil
in the positive-character convention. -/
def cmp99FlatPeriodicLaplacianSymbol (k : FinBox d N) : ℂ :=
  ∑ i : Fin d,
    (2 - ZMod.stdAddChar ((k i).val : ZMod N) -
      ZMod.stdAddChar (-((k i).val : ZMod N)))

/-- Exact Fourier eigenvalue identity for the scalar complex stencil.  This
is the diagonalization step only; it does not silently complexify the real
physical fibre. -/
theorem cmp99FlatPeriodicComplexStencil_fourierMode
    (k x : FinBox d N) :
    cmp99FlatPeriodicComplexStencil (cmp99FlatFourierMode k) x =
      cmp99FlatPeriodicLaplacianSymbol k * cmp99FlatFourierMode k x := by
  unfold cmp99FlatPeriodicComplexStencil cmp99FlatPeriodicLaplacianSymbol
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [cmp99FlatFourierMode_shift, cmp99FlatFourierMode_shiftBack]
  ring

end

end YangMills.RG
