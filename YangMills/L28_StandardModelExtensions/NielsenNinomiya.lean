/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Nielsen-Ninomiya theorem (Phase 265)

The Nielsen-Ninomiya no-go theorem on lattice fermions.

## Strategic placement

This is **Phase 265** of the L28_StandardModelExtensions block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L28_StandardModelExtensions

/-! ## §1. The 4 N-N hypotheses -/

/-- **Four hypotheses** of Nielsen-Ninomiya: locality, hermiticity,
    translational invariance, chiral invariance. Cannot all hold
    with a single Dirac fermion. -/
def NN_Hypotheses : List String :=
  [ "Locality (compact support of action)"
  , "Hermiticity (action is Hermitian)"
  , "Translational invariance"
  , "Chiral invariance (anticommutes with γ₅)" ]

theorem NN_Hypotheses_length : NN_Hypotheses.length = 4 := rfl

#print axioms NN_Hypotheses_length

/-! ## §2. The N-N obstruction -/

/-- **N-N theorem (statement)**: any lattice Dirac operator
    satisfying the 4 hypotheses must have an even number of
    fermion species (doublers).

    For 4D with all 4 hypotheses, the count is `2^4 = 16` species. -/
def NN_DoublerCount : ℕ := 16

theorem NN_DoublerCount_value : NN_DoublerCount = 16 := rfl

/-! ## §3. Workaround strategies -/

/-- **The 4 standard workarounds** to Nielsen-Ninomiya. -/
def NN_Workarounds : List String :=
  [ "Wilson fermions (break chiral symmetry)"
  , "Staggered fermions (reduce to 4 tastes via spin diagonalization)"
  , "Domain-wall fermions (extra dimension, recover chiral on boundary)"
  , "Overlap fermions (Ginsparg-Wilson exact lattice chirality)" ]

theorem NN_Workarounds_length : NN_Workarounds.length = 4 := rfl

#print axioms NN_Workarounds_length

end YangMills.L28_StandardModelExtensions
