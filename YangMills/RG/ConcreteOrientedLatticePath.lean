/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.OrientedLatticePath
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

/-!
# Non-vacuity of oriented paths on the periodic box

The abstract geometry interface does not assert graph connectivity.  For the
actual periodic-box instance, however, positive coordinate edges generate the
whole torus.  This file constructs the elementary step and proves that a
literal oriented path exists between every two sites.

The resulting choice is deliberately noncanonical and carries no length or
block-stay estimate.  It is a non-vacuity producer for contour systems, not the
source selection of `Gamma^(j)_{y,x}`.
-/

namespace YangMills.RG

open YangMills

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G]

/-- The single positive edge in direction `i`. -/
def positiveCoordinatePath (x : FinBox d N) (i : Fin d) :
    OrientedLatticePath (G := G) x (x.shift i) where
  edges := [⟨x, i, true⟩]
  isPath := by
    constructor
    · rfl
    · trivial
  ends := rfl

/-- Every two sites of the concrete periodic box are joined by a literal
oriented edge path. -/
theorem nonempty_orientedLatticePath (a b : FinBox d N) :
    Nonempty (OrientedLatticePath (G := G) a b) := by
  let P : FinBox d N → Prop := fun x =>
    Nonempty (OrientedLatticePath (G := G) x b)
  have hshift : ∀ (x : FinBox d N) (i : Fin d), P (x.shift i) = P x := by
    intro x i
    apply propext
    constructor
    · rintro ⟨Gamma⟩
      exact ⟨(positiveCoordinatePath (G := G) x i).trans Gamma⟩
    · rintro ⟨Gamma⟩
      exact ⟨(positiveCoordinatePath (G := G) x i).symm.trans Gamma⟩
  have hconst : ∀ x : FinBox d N, P x = P (default : FinBox d N) :=
    FinBox.eq_default_of_shift_invariant P hshift
  have hb : P b := ⟨OrientedLatticePath.refl (G := G) b⟩
  have hdefault : P (default : FinBox d N) := Eq.mp (hconst b) hb
  exact Eq.mpr (hconst a) hdefault

/-- A noncomputably selected concrete path between any two periodic sites. -/
noncomputable def concreteOrientedLatticePath (a b : FinBox d N) :
    OrientedLatticePath (G := G) a b :=
  Classical.choice (nonempty_orientedLatticePath (G := G) a b)

end YangMills.RG
