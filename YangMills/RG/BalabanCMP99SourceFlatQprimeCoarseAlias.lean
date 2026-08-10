/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimeFourierModeAction

/-!
# Coarse reciprocal alias of one flat `Q'` Fourier mode

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the compiler.

After the exact one-block average, the surviving fine mode is sampled at the
literal block basepoint.  This module constructs the corresponding coarse
reciprocal alias coordinatewise by reduction modulo `N'`.  It then proves,
from the standard additive characters themselves, that the fine character at
`M * y` is exactly the coarse character at `y`.

No alias or phase equality is accepted as data.  The conclusion is still
scalar and complex: it does not yet complexify the physical Lie fibre,
identify the weighted adjoint, diagonalize `Q'^* Q'`, construct an inverse or
transport to a regional Green operator.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d M N' : ℕ} [NeZero M] [NeZero N']

/-- The literal coarse reciprocal alias of a fine periodic momentum. -/
def cmp99SourceFlatQprimeCoarseAlias
    (k : FinBox d (M * N')) : FinBox d N' :=
  fun mu => ⟨(k mu).val % N',
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N'))⟩

@[simp] theorem cmp99SourceFlatQprimeCoarseAlias_apply_val
    (k : FinBox d (M * N')) (mu : Fin d) :
    (cmp99SourceFlatQprimeCoarseAlias k mu).val = (k mu).val % N' := rfl

/-- Casting a reduced natural coordinate into its coarse `ZMod` removes the
explicit remainder. -/
private lemma cmp99SourceFlatQprime_natCast_mod_zmod (a : ℕ) :
    ((a % N' : ℕ) : ZMod N') = (a : ZMod N') := by
  conv_rhs => rw [← Nat.div_add_mod a N']
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- Restricting the standard character of the fine torus to a multiple of
the block scale gives the standard character of the coarse torus. -/
private theorem cmp99SourceFlatQprime_stdAddChar_mul_blockScale
    (a : ℤ) :
    ZMod.stdAddChar (((M : ℤ) * a : ℤ) : ZMod (M * N')) =
      ZMod.stdAddChar (a : ZMod N') := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  have hM : (M : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  have hN : (N' : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N')
  congr 1
  push_cast
  field_simp [hM, hN]
  ring

/-- Coordinatewise character equality at the canonical block basepoint. -/
theorem cmp99SourceFlatQprime_coordinateCharacter_blockBasepoint
    (k : FinBox d (M * N')) (y : FinBox d N') (mu : Fin d) :
    ZMod.stdAddChar
        (((k mu).val : ZMod (M * N')) *
          (((blockBasepoint M N' y) mu).val : ZMod (M * N'))) =
      ZMod.stdAddChar
        (((cmp99SourceFlatQprimeCoarseAlias k mu).val : ZMod N') *
          ((y mu).val : ZMod N')) := by
  rw [show
      ((k mu).val : ZMod (M * N')) *
          (((blockBasepoint M N' y) mu).val : ZMod (M * N')) =
        (((M : ℤ) * (((k mu).val * (y mu).val : ℕ) : ℤ) : ℤ) :
          ZMod (M * N')) by
    simp only [blockBasepoint]
    push_cast
    ring]
  rw [cmp99SourceFlatQprime_stdAddChar_mul_blockScale]
  congr 1
  simp only [cmp99SourceFlatQprimeCoarseAlias_apply_val]
  rw [cmp99SourceFlatQprime_natCast_mod_zmod]
  push_cast
  ring

/-- Every flat Fourier mode is the product of its coordinate characters. -/
theorem cmp99FlatFourierMode_eq_coordinateProduct
    {N : ℕ} [NeZero N] (k x : FinBox d N) :
    cmp99FlatFourierMode k x =
      ∏ mu : Fin d,
        ZMod.stdAddChar
          (((k mu).val : ZMod N) * ((x mu).val : ZMod N)) := by
  unfold cmp99FlatFourierMode cmp99FlatFourierPhase
  let psi : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  have hprod : ∀ s : Finset (Fin d),
      psi (∑ mu ∈ s,
          ((k mu).val : ZMod N) * ((x mu).val : ZMod N)) =
        ∏ mu ∈ s,
          psi (((k mu).val : ZMod N) * ((x mu).val : ZMod N)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert mu s hmu ih =>
        rw [Finset.sum_insert hmu, Finset.prod_insert hmu,
          AddChar.map_add_eq_mul, ih]
  exact hprod Finset.univ

/-- The fine mode sampled at a canonical block basepoint is literally the
coarse mode at the coordinatewise reciprocal alias. -/
theorem cmp99FlatFourierMode_blockBasepoint_eq_coarseAlias
    (k : FinBox d (M * N')) (y : FinBox d N') :
    cmp99FlatFourierMode k (blockBasepoint M N' y) =
      cmp99FlatFourierMode (cmp99SourceFlatQprimeCoarseAlias k) y := by
  rw [cmp99FlatFourierMode_eq_coordinateProduct,
    cmp99FlatFourierMode_eq_coordinateProduct]
  apply Finset.prod_congr rfl
  intro mu _
  exact cmp99SourceFlatQprime_coordinateCharacter_blockBasepoint k y mu

/-- Exact scalar fine-to-coarse mode action of one source-normalized flat
block average.  Both the amplitude and the coarse reciprocal alias are now
literal objects rather than inputs. -/
theorem cmp99SourceFlatQprimeWeightedBlockSum_fourierMode_eq_coarseAlias
    (k : FinBox d (M * N')) (y : FinBox d N') :
    (cmp99SourceBlockAverageWeight M d : ℂ) *
        ∑ r : FinBox d M,
          cmp99FlatFourierMode k (cmp99BlockEmbed y r) =
      cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum k) *
        cmp99FlatFourierMode (cmp99SourceFlatQprimeCoarseAlias k) y := by
  rw [cmp99SourceFlatQprimeWeightedBlockSum_fourierMode,
    cmp99FlatFourierMode_blockBasepoint_eq_coarseAlias]

end

end YangMills.RG
