/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimeFourierAmplitude
import YangMills.RG.BalabanCMP99SourceFlatQprimeBlockOffsetEquiv
import YangMills.RG.BalabanCMP99SourceFlatFourierSymbolDictionary

/-!
# Exact flat one-block `Q'` action on a fine Fourier mode

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the compiler.

The fine Fourier mode lives on `FinBox d (M * N')`, whereas one application
of the CMP99 average produces a function of the coarse owner block.  This
module keeps those carriers distinct.  It first splits the fine character at
the literal block embedding into its block-basepoint phase and its internal
offset phase.  The latter is then identified with the already sealed CMP89
finite geometric amplitude at the explicit signed momentum
`-M * p_fine`.

Honest scope: the conclusion is the exact normalized sum over one complete
owner block.  It does not identify the remaining block-basepoint phase with a
coarse Fourier mode, choose a reciprocal alias, complexify the physical real
fibre, identify the weighted adjoint, or diagonalize `Q'^* Q'`.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d M N' : ℕ} [NeZero M] [NeZero N']

/-- The additive fine-lattice phase carried only by an internal block
offset.  Its modulus remains the fine torus size `M * N'`. -/
def cmp99SourceFlatQprimeFineOffsetPhase
    (k : FinBox d (M * N')) (r : FinBox d M) : ZMod (M * N') :=
  ∑ mu : Fin d,
    ((k mu).val : ZMod (M * N')) * ((r mu).val : ZMod (M * N'))

omit [NeZero N'] in
/-- The fine phase at an embedded block site is exactly the sum of the phase
at the canonical block basepoint and the internal-offset phase. -/
theorem cmp99FlatFourierPhase_blockEmbed
    (k : FinBox d (M * N')) (y : FinBox d N') (r : FinBox d M) :
    cmp99FlatFourierPhase k (cmp99BlockEmbed y r) =
      cmp99FlatFourierPhase k (blockBasepoint M N' y) +
        cmp99SourceFlatQprimeFineOffsetPhase k r := by
  unfold cmp99FlatFourierPhase cmp99SourceFlatQprimeFineOffsetPhase
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mu _
  simp only [cmp99BlockEmbed, blockBasepoint]
  push_cast
  ring

/-- The positive fine-lattice character carried by an internal block
offset. -/
def cmp99SourceFlatQprimeFineOffsetCharacter
    (k : FinBox d (M * N')) (r : FinBox d M) : ℂ :=
  ZMod.stdAddChar (cmp99SourceFlatQprimeFineOffsetPhase k r)

omit [NeZero N'] in
/-- Exact character factorization at the literal block embedding. -/
theorem cmp99FlatFourierMode_blockEmbed
    (k : FinBox d (M * N')) (y : FinBox d N') (r : FinBox d M) :
    cmp99FlatFourierMode k (cmp99BlockEmbed y r) =
      cmp99FlatFourierMode k (blockBasepoint M N' y) *
        cmp99SourceFlatQprimeFineOffsetCharacter k r := by
  unfold cmp99FlatFourierMode cmp99SourceFlatQprimeFineOffsetCharacter
  rw [cmp99FlatFourierPhase_blockEmbed, AddChar.map_add_eq_mul]

/-- The momentum argument whose CMP89 negative exponential is the positive
fine-lattice offset character.  The sign and the factor `M` are explicit so
that no orientation convention is hidden in the later alias dictionary. -/
def cmp99SourceFlatQprimeAmplitudeMomentum
    (k : FinBox d (M * N')) : Fin d → ℂ :=
  fun mu => -((M : ℂ) * (cmp99FlatDiscreteMomentum k mu : ℂ))

/-- One CMP89 geometric-series base at the signed amplitude momentum is the
positive standard character of the corresponding fine momentum. -/
theorem cmp89Eq245EntireAverageBase_amplitudeMomentum
    (k : FinBox d (M * N')) (mu : Fin d) :
    cmp89Eq245EntireAverageBase M
        (cmp99SourceFlatQprimeAmplitudeMomentum k mu) =
      ZMod.stdAddChar ((k mu).val : ZMod (M * N')) := by
  rw [cmp99Flat_stdAddChar_eq_exp_discreteMomentum]
  unfold cmp89Eq245EntireAverageBase
    cmp99SourceFlatQprimeAmplitudeMomentum
  have hM : (M : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  congr 1
  field_simp [hM]

omit [NeZero N'] in
/-- The additive offset character is the coordinatewise product character.
This is the only use of the additive-character algebra in the block sum. -/
theorem cmp99SourceFlatQprimeFineOffsetCharacter_eq_prod
    (k : FinBox d (M * N')) (r : FinBox d M) :
    cmp99SourceFlatQprimeFineOffsetCharacter k r =
      ∏ mu : Fin d,
        ZMod.stdAddChar ((k mu).val : ZMod (M * N')) ^ (r mu).val := by
  unfold cmp99SourceFlatQprimeFineOffsetCharacter
    cmp99SourceFlatQprimeFineOffsetPhase
  let psi : AddChar (ZMod (M * N')) ℂ := ZMod.stdAddChar
  have hprod : ∀ s : Finset (Fin d),
      psi (∑ mu ∈ s,
          ((k mu).val : ZMod (M * N')) *
            ((r mu).val : ZMod (M * N'))) =
        ∏ mu ∈ s,
          psi ((k mu).val : ZMod (M * N')) ^ (r mu).val := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert mu s hmu ih =>
        rw [Finset.sum_insert hmu, Finset.prod_insert hmu,
          AddChar.map_add_eq_mul, ih]
        congr 1
        rw [← AddChar.map_nsmul_eq_pow]
        congr 1
        simp [nsmul_eq_mul, mul_comm]
  exact hprod Finset.univ

/-- The fine-lattice offset character is literally the offset character used
by the sealed CMP89 amplitude, at the explicit signed momentum. -/
theorem cmp99SourceFlatQprimeFineOffsetCharacter_eq_sourceCharacter
    (k : FinBox d (M * N')) (r : FinBox d M) :
    cmp99SourceFlatQprimeFineOffsetCharacter k r =
      cmp99SourceFlatQprimeOffsetCharacter d M
        (cmp99SourceFlatQprimeAmplitudeMomentum k) r := by
  rw [cmp99SourceFlatQprimeFineOffsetCharacter_eq_prod]
  unfold cmp99SourceFlatQprimeOffsetCharacter
  apply Finset.prod_congr rfl
  intro mu _
  rw [cmp89Eq245EntireAverageBase_amplitudeMomentum]

/-- Exact scalar action of the source-normalized flat one-block average on a
fine Fourier mode.  The output is deliberately left as the fine mode sampled
at the block basepoint; the coarse-mode/alias identification is a separate
dictionary obligation. -/
theorem cmp99SourceFlatQprimeWeightedBlockSum_fourierMode
    (k : FinBox d (M * N')) (y : FinBox d N') :
    (cmp99SourceBlockAverageWeight M d : ℂ) *
        ∑ r : FinBox d M,
          cmp99FlatFourierMode k (cmp99BlockEmbed y r) =
      cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum k) *
        cmp99FlatFourierMode k (blockBasepoint M N' y) := by
  calc
    (cmp99SourceBlockAverageWeight M d : ℂ) *
          ∑ r : FinBox d M,
            cmp99FlatFourierMode k (cmp99BlockEmbed y r) =
        (cmp99SourceBlockAverageWeight M d : ℂ) *
          ∑ r : FinBox d M,
            cmp99SourceFlatQprimeOffsetCharacter d M
                (cmp99SourceFlatQprimeAmplitudeMomentum k) r *
              cmp99FlatFourierMode k (blockBasepoint M N' y) := by
            congr 1
            apply Finset.sum_congr rfl
            intro r _
            rw [cmp99FlatFourierMode_blockEmbed,
              cmp99SourceFlatQprimeFineOffsetCharacter_eq_sourceCharacter]
            ring
    _ = ((cmp99SourceBlockAverageWeight M d : ℂ) *
          ∑ r : FinBox d M,
            cmp99SourceFlatQprimeOffsetCharacter d M
              (cmp99SourceFlatQprimeAmplitudeMomentum k) r) *
          cmp99FlatFourierMode k (blockBasepoint M N' y) := by
            rw [← Finset.sum_mul]
            ring
    _ = cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum k) *
        cmp99FlatFourierMode k (blockBasepoint M N' y) := by
          rw [← cmp99SourceFlatQprimeOffsetAmplitude_eq_entireAverageAmplitude]
          unfold cmp99SourceFlatQprimeOffsetAmplitude
          rw [Fintype.piFinset_univ]

end

end YangMills.RG
