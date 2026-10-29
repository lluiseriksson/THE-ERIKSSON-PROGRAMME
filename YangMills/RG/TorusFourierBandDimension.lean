/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib

/-!
# Concrete finite-torus Fourier cube: independence and dimension

The functions and subspace are constructed here, rather than supplied as a
dimension hypothesis. Complex-valued profiles, viewed over the reals, have
twice the complex dimension. This is NOT the real scalar Fourier band: its
transport into pairs of internal real coordinates of physical cochains remains
separate, as do the Hodge energy and norm-preservation obligations.
-/

namespace YangMills.RG

open Module
open scoped BigOperators

variable {d n : ℕ} [NeZero n]

/-- The character with frequency k on a product of finite cyclic groups. -/
noncomputable def torusFourierCharacter (k : Fin d → ZMod n) :
    AddChar (Fin d → ZMod n) ℂ where
  toFun x := ZMod.stdAddChar (∑ i : Fin d, k i * x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact AddChar.map_add_eq_mul _ _ _

/-- Distinct frequency vectors give distinct characters, including d=0. -/
theorem torusFourierCharacter_injective :
    Function.Injective (torusFourierCharacter (d := d) (n := n)) := by
  classical
  intro k l hkl
  funext i
  apply ZMod.injective_stdAddChar
  have hi := congrArg (fun chi : AddChar (Fin d → ZMod n) ℂ =>
    chi (Pi.single i (1 : ZMod n))) hkl
  simpa [torusFourierCharacter, Pi.single_apply] using hi

/-- Independence is proved for the actual functions on the actual torus. -/
theorem torusFourierProfiles_linearIndependent :
    LinearIndependent ℂ (fun k : Fin d → ZMod n =>
      (torusFourierCharacter k : (Fin d → ZMod n) → ℂ)) := by
  exact (AddChar.linearIndependent (Fin d → ZMod n) ℂ).comp _
    torusFourierCharacter_injective

/-- Coordinate labels 0,...,2R become the centered residues -R,...,R. -/
def centeredFourierFrequency (R : ℕ) (k : Fin d → Fin (2 * R + 1)) :
    Fin d → ZMod n := fun i => ((k i : ℕ) : ZMod n) - (R : ZMod n)

/-- There is no modular aliasing when 2R<n. -/
theorem centeredFourierFrequency_injective (R : ℕ) (hR : 2 * R < n) :
    Function.Injective (centeredFourierFrequency (d := d) (n := n) R) := by
  intro k l hkl
  funext i
  apply Fin.ext
  have heq := congrArg (fun z : ZMod n => z + (R : ZMod n)) (congrFun hkl i)
  have heq' : ((k i : ℕ) : ZMod n) = ((l i : ℕ) : ZMod n) := by
    simpa [centeredFourierFrequency] using heq
  have hk : (k i : ℕ) < n := by have := (k i).isLt; omega
  have hl : (l i : ℕ) < n := by have := (l i).isLt; omega
  have hv := congrArg ZMod.val heq'
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl] using hv

/-- The concrete centered-cube profiles. -/
noncomputable def centeredFourierProfile (R : ℕ) (k : Fin d → Fin (2 * R + 1)) :
    (Fin d → ZMod n) → ℂ :=
  torusFourierCharacter (centeredFourierFrequency R k)

theorem centeredFourierProfiles_linearIndependent (R : ℕ) (hR : 2 * R < n) :
    LinearIndependent ℂ (centeredFourierProfile (d := d) (n := n) R) := by
  exact torusFourierProfiles_linearIndependent.comp _
    (centeredFourierFrequency_injective R hR)

/-- The band is a concrete span, with no assumed basis or dimension. -/
noncomputable def centeredFourierBand (d n R : ℕ) [NeZero n] :
    Submodule ℂ ((Fin d → ZMod n) → ℂ) :=
  Submodule.span ℂ (Set.range (centeredFourierProfile (d := d) (n := n) R))

theorem centeredFourierBand_finrank_complex (R : ℕ) (hR : 2 * R < n) :
    finrank ℂ (centeredFourierBand d n R) = (2 * R + 1) ^ d := by
  rw [centeredFourierBand,
    finrank_span_eq_card (centeredFourierProfiles_linearIndependent R hR)]
  simp

/-- Restriction of scalars counts two real internal coordinates per complex
profile. It does not count two independent real scalar profiles per frequency. -/
theorem centeredFourierBand_finrank_real (R : ℕ) (hR : 2 * R < n) :
    finrank ℝ (centeredFourierBand d n R) = 2 * (2 * R + 1) ^ d := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (centeredFourierBand d n R),
    Complex.finrank_real_complex, centeredFourierBand_finrank_complex R hR]

end YangMills.RG
