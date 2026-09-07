/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFourierSymbolDictionary

/-!
# Complexification of the physical CMP99 Lie-coordinate fibre

The physical zero-cochain fibre is the real Euclidean coordinate model
`SUNLieCoord Nc`.  This module embeds it coordinatewise into the corresponding
complex Euclidean space, proves that the embedding commutes with the literal
flat stencil, and diagonalizes the resulting complex-fibre stencil by the
already sealed periodic character.

Honest scope: no generated `Q'` symbol or adjoint, Green inverse, gauge
transport or regional compression is constructed here.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d N Nc : ℕ} [NeZero N]

/-- Complex coordinate space on the same literal Lie-coordinate index set as
`SUNLieCoord Nc`. -/
abbrev SUNLieComplexCoord (Nc : ℕ) :=
  EuclideanSpace ℂ (Fin (Nc ^ 2 - 1))

/-- Coordinatewise scalar extension of the physical real Lie-coordinate
fibre.  The map is explicitly real-linear; no complex fibre is identified
definitionally with `SUNLieCoord Nc`. -/
def cmp99SUNLieCoordComplexificationLM (Nc : ℕ) :
    SUNLieCoord Nc →ₗ[ℝ] SUNLieComplexCoord Nc where
  toFun X := WithLp.toLp 2 fun a => (X a : ℂ)
  map_add' X Y := by
    ext a
    simp
  map_smul' r X := by
    ext a
    simp

@[simp]
theorem cmp99SUNLieCoordComplexificationLM_apply
    (X : SUNLieCoord Nc) (a : Fin (Nc ^ 2 - 1)) :
    cmp99SUNLieCoordComplexificationLM Nc X a = (X a : ℂ) := by
  rfl

/-- The coordinatewise complexification loses no physical real vector. -/
theorem cmp99SUNLieCoordComplexificationLM_injective :
    Function.Injective (cmp99SUNLieCoordComplexificationLM Nc) := by
  intro X Y h
  ext a
  apply Complex.ofReal_injective
  simpa using congrArg (fun Z : SUNLieComplexCoord Nc => Z a) h

/-- Symmetric nearest-neighbour stencil on the explicitly complexified
physical fibre. -/
def cmp99FlatPeriodicComplexFibreStencil
    (phi : FinBox d N → SUNLieComplexCoord Nc) (x : FinBox d N) :
    SUNLieComplexCoord Nc :=
  ∑ i : Fin d,
    ((phi x - phi (x.shift i)) - (phi (x.shiftBack i) - phi x))

/-- Coordinatewise complexification commutes exactly with the literal flat
physical stencil. -/
theorem cmp99FlatPeriodicComplexFibreStencil_complexification
    (phi : PhysicalGaugeZeroCochain d N Nc) (x : FinBox d N) :
    cmp99FlatPeriodicComplexFibreStencil
        (fun y => cmp99SUNLieCoordComplexificationLM Nc (phi y)) x =
      cmp99SUNLieCoordComplexificationLM Nc
        (cmp99FlatPeriodicLaplacianStencil phi x) := by
  ext a
  simp [cmp99FlatPeriodicComplexFibreStencil,
    cmp99FlatPeriodicLaplacianStencil]

/-- Vector-valued Fourier mode in the explicit complexified physical fibre. -/
def cmp99FlatComplexFibreFourierMode
    (k : FinBox d N) (v : SUNLieComplexCoord Nc) :
    FinBox d N → SUNLieComplexCoord Nc :=
  fun x => cmp99FlatFourierMode k x • v

/-- The complex-fibre flat stencil has the literal scalar character
eigenvalue, with no choice of basis vector or Fourier family supplied. -/
theorem cmp99FlatPeriodicComplexFibreStencil_fourierMode
    (k x : FinBox d N) (v : SUNLieComplexCoord Nc) :
    cmp99FlatPeriodicComplexFibreStencil
        (cmp99FlatComplexFibreFourierMode k v) x =
      cmp99FlatPeriodicLaplacianSymbol k •
        cmp99FlatComplexFibreFourierMode k v x := by
  ext a
  unfold cmp99FlatPeriodicComplexFibreStencil
    cmp99FlatComplexFibreFourierMode cmp99FlatPeriodicLaplacianSymbol
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [cmp99FlatFourierMode_shift, cmp99FlatFourierMode_shiftBack]
  ring

/-- The vector-valued complexified physical stencil is diagonalized by the
printed CMP89 unit-lattice symbol at the literal discrete momentum. -/
theorem cmp99FlatPeriodicComplexFibreStencil_fourierMode_cmp89Unit
    (k x : FinBox d N) (v : SUNLieComplexCoord Nc) :
    cmp99FlatPeriodicComplexFibreStencil
        (cmp99FlatComplexFibreFourierMode k v) x =
      (cmp89Eq249UnitLaplacianSymbol d 0
          (cmp99FlatDiscreteMomentum k) : ℂ) •
        cmp99FlatComplexFibreFourierMode k v x := by
  rw [cmp99FlatPeriodicComplexFibreStencil_fourierMode,
    cmp99FlatPeriodicLaplacianSymbol_eq_cmp89Unit]

end

end YangMills.RG
