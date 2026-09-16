/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq248EntireFourierSymbols
import YangMills.RG.BalabanCMP99SourceFlatFourierStencil

/-!
# Flat CMP99 character symbol versus the printed CMP89 symbol

This module fixes the discrete physical momentum `2*pi*k/N` and identifies
the scalar character eigenvalue of the flat periodic CMP99 stencil with the
unit-lattice Laplacian symbol printed in CMP89 (2.49).  Positive and negative
characters are transported separately before their opposite-momentum product
is compared with the source symbol.

Honest scope: this remains a scalar complex identity.  It does not
complexify the real `SUNLieCoord Nc` fibre, diagonalize the generated `Q'`
term, construct a Green inverse or perform regional compression.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d N : ℕ} [NeZero N]

/-- Literal real momentum associated with a periodic `ZMod` character. -/
def cmp99FlatDiscreteMomentum (k : FinBox d N) : Fin d → ℝ :=
  fun i => 2 * Real.pi * (k i).val / (N : ℝ)

/-- The positive standard character is the positive exponential at the
literal discrete momentum. -/
theorem cmp99Flat_stdAddChar_eq_exp_discreteMomentum
    (k : FinBox d N) (i : Fin d) :
    ZMod.stdAddChar ((k i).val : ZMod N) =
      Complex.exp (Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ)) := by
  have h := ZMod.stdAddChar_coe (N := N) ((k i).val : ℤ)
  convert h using 1
  · norm_num
  · unfold cmp99FlatDiscreteMomentum
    push_cast
    congr 1
    ring

/-- The negative standard character is the opposite-momentum exponential. -/
theorem cmp99Flat_stdAddChar_neg_eq_exp_neg_discreteMomentum
    (k : FinBox d N) (i : Fin d) :
    ZMod.stdAddChar (-((k i).val : ZMod N)) =
      Complex.exp (Complex.I * (-(cmp99FlatDiscreteMomentum k i) : ℂ)) := by
  rw [AddChar.map_neg_eq_inv,
    cmp99Flat_stdAddChar_eq_exp_discreteMomentum, ← Complex.exp_neg]
  congr 1
  ring

/-- One character eigenvalue summand is exactly the opposite-momentum entire
pairing used to continue the printed unit-lattice difference symbol. -/
theorem cmp99Flat_characterPair_eq_entireUnitDifferencePair
    (k : FinBox d N) (i : Fin d) :
    (2 - ZMod.stdAddChar ((k i).val : ZMod N) -
        ZMod.stdAddChar (-((k i).val : ZMod N))) =
      cmp89Eq245EntireScaledDifference 1
          (cmp99FlatDiscreteMomentum k i : ℂ) *
        cmp89Eq245EntireScaledDifference 1
          (-(cmp99FlatDiscreteMomentum k i : ℂ)) := by
  rw [cmp99Flat_stdAddChar_eq_exp_discreteMomentum,
    cmp99Flat_stdAddChar_neg_eq_exp_neg_discreteMomentum]
  unfold cmp89Eq245EntireScaledDifference
  norm_num
  have hmul :
      Complex.exp
          (Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ)) *
        Complex.exp
          (-(Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    2 - Complex.exp
          (Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ)) -
        Complex.exp
          (-(Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ))) =
        1 - Complex.exp
              (Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ)) -
          Complex.exp
              (-(Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ))) +
          Complex.exp
              (Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ)) *
            Complex.exp
              (-(Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ))) := by
      rw [hmul]
      ring
    _ =
        (Complex.exp
              (-(Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ))) - 1) *
          (Complex.exp
              (Complex.I * (cmp99FlatDiscreteMomentum k i : ℂ)) - 1) := by
      ring

/-- At lattice spacing one, the scaled CMP89 symbol is definitionally the
unit-lattice symbol used in (2.49). -/
theorem cmp89Eq245ScaledLaplacianSymbol_one_eq_unit
    (mass : ℝ) (p : Fin d → ℝ) :
    cmp89Eq245ScaledLaplacianSymbol d 1 mass p =
      cmp89Eq249UnitLaplacianSymbol d mass p := by
  unfold cmp89Eq245ScaledLaplacianSymbol
    cmp89Eq249UnitLaplacianSymbol
    cmp89Eq245ScaledDifferenceNorm cmp89Eq249UnitDifferenceNorm
  norm_num

/-- The scalar periodic CMP99 eigenvalue is the printed mass-zero
unit-lattice Laplacian symbol at the literal discrete momentum. -/
theorem cmp99FlatPeriodicLaplacianSymbol_eq_cmp89Unit
    (k : FinBox d N) :
    cmp99FlatPeriodicLaplacianSymbol k =
      (cmp89Eq249UnitLaplacianSymbol d 0
        (cmp99FlatDiscreteMomentum k) : ℂ) := by
  calc
    cmp99FlatPeriodicLaplacianSymbol k =
        cmp89Eq245EntireScaledLaplacianSymbol d 1 0
          (fun i => (cmp99FlatDiscreteMomentum k i : ℂ)) := by
      unfold cmp99FlatPeriodicLaplacianSymbol
        cmp89Eq245EntireScaledLaplacianSymbol
      push_cast
      norm_num only [zero_pow, OfNat.ofNat_ne_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i _
      exact cmp99Flat_characterPair_eq_entireUnitDifferencePair k i
    _ = (cmp89Eq245ScaledLaplacianSymbol d 1 0
          (cmp99FlatDiscreteMomentum k) : ℂ) :=
      cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq d 1 0
        (cmp99FlatDiscreteMomentum k)
    _ = (cmp89Eq249UnitLaplacianSymbol d 0
          (cmp99FlatDiscreteMomentum k) : ℂ) := by
      rw [cmp89Eq245ScaledLaplacianSymbol_one_eq_unit]

end

end YangMills.RG
