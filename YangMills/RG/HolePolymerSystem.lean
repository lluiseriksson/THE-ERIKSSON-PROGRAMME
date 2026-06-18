/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.KP.Basic
import YangMills.RG.ModifiedMetric

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

/-- The **holes-respected polymer system** on the cube lattice.
    Polymers are nonempty, connected finsets of cubes that respect the hole family H.
    Two polymers are incompatible if they overlap. -/
noncomputable def holePolymerSystem {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) :
    KP.PolymerSystem where
  Polymer := { X : Finset (Cube d L) // X.Nonempty ∧ cubeConnected X ∧ polymerWithHoles H X }
  incomp X Y := ¬ Disjoint X.1 Y.1
  incomp_symm := by
    intro X Y h hd
    exact h hd.symm
  incomp_self := by
    intro X hd
    obtain ⟨x, hx⟩ := X.2.1
    exact (Finset.disjoint_left.mp hd hx) hx
  activity X := z X.1

noncomputable instance {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) :
    Fintype (holePolymerSystem H z).Polymer :=
  inferInstanceAs (Fintype { X : Finset (Cube d L) // X.Nonempty ∧ cubeConnected X ∧ polymerWithHoles H X })

end YangMills.RG
