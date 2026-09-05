/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedAmbientLaplacian
import YangMills.RG.BalabanCMP99PhysicalFibreComplexification

/-!
# Flat generated complex-stencil dictionary

The generated closed-form fine-box equivalence is a dependent cast along the
sealed side-length equality.  This module proves propositionally that the cast
commutes with both periodic nearest-neighbour steps, then transports the
canonical generated complex zero extension through the literal flat stencil.

No spacing-power, generated mass, full precision, inverse or Green operator is
asserted here.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

omit [NeZero d] in
private theorem finBoxEquivCast_shift
    {A B : ℕ} [NeZero A] [NeZero B]
    (h : A = B) (x : FinBox d A) (i : Fin d) :
    Equiv.cast (congrArg (FinBox d) h) (x.shift i) =
      (Equiv.cast (congrArg (FinBox d) h) x).shift i := by
  subst B
  rfl

omit [NeZero d] in
private theorem finBoxEquivCast_shiftBack
    {A B : ℕ} [NeZero A] [NeZero B]
    (h : A = B) (x : FinBox d A) (i : Fin d) :
    Equiv.cast (congrArg (FinBox d) h) (x.shiftBack i) =
      (Equiv.cast (congrArg (FinBox d) h) x).shiftBack i := by
  subst B
  rfl

omit [NeZero d] in
/-- The generated closed-form fine-box equivalence commutes with the positive
periodic step.  The equality is propositional across the two dependent box
types. -/
theorem cmp99GeneratedFineBoxOneBlockEquiv_shift
    (depth : ℕ)
    (x : FinBox d (cmp99RegionalLatticeSize M N depth)) (i : Fin d) :
    cmp99GeneratedFineBoxOneBlockEquiv (d := d) M N depth (x.shift i) =
      (cmp99GeneratedFineBoxOneBlockEquiv
        (d := d) M N depth x).shift i := by
  exact finBoxEquivCast_shift
    (cmp99RegionalLatticeSize_eq_pow_mul M N depth) x i

omit [NeZero d] in
/-- The generated closed-form fine-box equivalence commutes with the negative
periodic step.  The equality is propositional across the two dependent box
types. -/
theorem cmp99GeneratedFineBoxOneBlockEquiv_shiftBack
    (depth : ℕ)
    (x : FinBox d (cmp99RegionalLatticeSize M N depth)) (i : Fin d) :
    cmp99GeneratedFineBoxOneBlockEquiv (d := d) M N depth (x.shiftBack i) =
      (cmp99GeneratedFineBoxOneBlockEquiv
        (d := d) M N depth x).shiftBack i := by
  exact finBoxEquivCast_shiftBack
    (cmp99RegionalLatticeSize_eq_pow_mul M N depth) x i

namespace CMP99SourceGeneratedTerminalComplexFieldData

omit [NeZero d] [NeZero Nc] in
/-- The complex flat stencil of the canonical generated full-box field is the
coordinatewise complexification of the real flat stencil on its canonical
real zero extension.  Both neighbour orientations use the explicit generated
box transport above. -/
theorem complexStencil_apply_generatedBox_eq_complexification_realStencil
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (D : CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc) Omega depth)
    (x : FinBox d (cmp99RegionalLatticeSize M N (depth + 1))) :
    cmp99FlatPeriodicComplexFibreStencil D.complexZeroExtension
        (cmp99GeneratedFineBoxOneBlockEquiv
          (d := d) M N (depth + 1) x) =
      cmp99SUNLieCoordComplexificationLM Nc
        (cmp99FlatPeriodicLaplacianStencil D.realZeroExtension x) := by
  calc
    cmp99FlatPeriodicComplexFibreStencil D.complexZeroExtension
        (cmp99GeneratedFineBoxOneBlockEquiv
          (d := d) M N (depth + 1) x) =
        cmp99FlatPeriodicComplexFibreStencil
          (fun y => cmp99SUNLieCoordComplexificationLM Nc
            (D.realZeroExtension y)) x := by
      unfold cmp99FlatPeriodicComplexFibreStencil
      apply Finset.sum_congr rfl
      intro i _
      rw [← cmp99GeneratedFineBoxOneBlockEquiv_shift,
        ← cmp99GeneratedFineBoxOneBlockEquiv_shiftBack]
      simp only [
        complexZeroExtension_apply_eq_complexification_realZeroExtension]
    _ = cmp99SUNLieCoordComplexificationLM Nc
        (cmp99FlatPeriodicLaplacianStencil D.realZeroExtension x) :=
      cmp99FlatPeriodicComplexFibreStencil_complexification
        D.realZeroExtension x

end CMP99SourceGeneratedTerminalComplexFieldData

end

end YangMills.RG
