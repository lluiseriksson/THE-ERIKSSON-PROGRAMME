/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.MatrixRealization
import YangMills.RG.BalabanCMP116WilsonHessianUnitaryChart

/-!
# The defining matrix realization of SU(N)

This file supplies the physical instance promised by `MatrixRealization`:
special-unitary matrices act through their literal defining matrices, viewed
as units.  No representation is chosen noncomputably.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ}

/-- Forgetting determinant one is a literal monoid homomorphism. -/
def specialUnitaryToUnitaryHom (Nc : ℕ) : SUN Nc →* UN Nc where
  toFun := specialUnitaryToUnitary
  map_one' := specialUnitaryToUnitary_one
  map_mul' := specialUnitaryToUnitary_mul

/-- The defining representation of `SU(Nc)` as units of its matrix algebra. -/
def specialUnitaryMatrixUnitsHom (Nc : ℕ) :
    SUN Nc →* (Matrix (Fin Nc) (Fin Nc) ℂ)ˣ :=
  Unitary.toUnits.comp (specialUnitaryToUnitaryHom Nc)

/-- Physical `SU(Nc)` matrices instantiate the generic lattice realization
without changing their underlying matrix entries. -/
instance instMatrixRealizationSUN :
    MatrixRealization (SUN Nc) (Matrix (Fin Nc) (Fin Nc) ℂ) where
  rep := specialUnitaryMatrixUnitsHom Nc

@[simp] theorem specialUnitaryMatrixUnitsHom_val (U : SUN Nc) :
    ((specialUnitaryMatrixUnitsHom Nc U :
      (Matrix (Fin Nc) (Fin Nc) ℂ)ˣ) : Matrix (Fin Nc) (Fin Nc) ℂ) = U :=
  rfl

@[simp] theorem matrixRealizationSUN_val (U : SUN Nc) :
    ((MatrixRealization.rep U :
      (Matrix (Fin Nc) (Fin Nc) ℂ)ˣ) : Matrix (Fin Nc) (Fin Nc) ℂ) = U :=
  rfl

end

end YangMills.RG
