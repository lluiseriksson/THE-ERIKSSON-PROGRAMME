import Mathlib

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# SpecialUnitaryCompactCore — Layer topology-target

This file pins the **actual Mathlib names** available in the local snapshot and
packages the honest compactness targets for the special unitary group.

What is done here:
* re-export the correct membership theorem for `Matrix.specialUnitaryGroup`,
* re-export the inclusion into `Matrix.unitaryGroup`,
* define the two honest compactness targets that the unconditional route needs:
  1. compactness of the subtype itself,
  2. compactness of its image inside the ambient matrix space.

What is **not** done here:
* this file does not yet prove compactness.
It only fixes the namespace and records the exact topological goal in Lean.
-/

noncomputable section

section NamePinning

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {α : Type*} [CommRing α] [StarRing α]

/-- Local alias for the special-unitary subtype carried by Mathlib. -/
abbrev SpecialUnitarySubtype :=
  ↥(Matrix.specialUnitaryGroup n α)

/-- Mathlib's actual membership characterization for the special unitary group.
-/
theorem mem_specialUnitaryGroup_iff'
    (A : Matrix n n α) :
    A ∈ Matrix.specialUnitaryGroup n α ↔
      A ∈ Matrix.unitaryGroup n α ∧ A.det = 1 := by
  simpa using (Matrix.mem_specialUnitaryGroup_iff (n := n) (α := α) (A := A))

/-- The special unitary group sits inside the unitary group. -/
theorem specialUnitaryGroup_le_unitaryGroup'
    : Matrix.specialUnitaryGroup n α ≤ Matrix.unitaryGroup n α := by
  exact Matrix.specialUnitaryGroup_le_unitaryGroup (n := n) (α := α)

/-- Any element of the special unitary group is, in particular, unitary. -/
theorem specialUnitarySubtype_mem_unitary
    (U : SpecialUnitarySubtype (n := n) (α := α)) :
    ((U : Matrix n n α) ∈ Matrix.unitaryGroup n α) := by
  exact (mem_specialUnitaryGroup_iff' (n := n) (α := α) (A := (U : Matrix n n α))).1 U.2 |>.1

/-- Any element of the special unitary group has determinant `1`. -/
theorem det_eq_one_of_specialUnitarySubtype
    (U : SpecialUnitarySubtype (n := n) (α := α)) :
    (U : Matrix n n α).det = 1 := by
  exact (mem_specialUnitaryGroup_iff' (n := n) (α := α) (A := (U : Matrix n n α))).1 U.2 |>.2

end NamePinning

section ComplexTargets

/-- The concrete subtype corresponding to `SU(m)` in the local Mathlib naming.
-/
abbrev SpecialUnitaryComplexSubtype (m : ℕ) :=
  ↥(Matrix.specialUnitaryGroup (Fin m) ℂ)

/-- Honest compactness target, subtype form:
the topological space underlying `SU(m)` should be compact. -/
def SpecialUnitaryCompactSubtypeTarget (m : ℕ) : Prop :=
  CompactSpace (SpecialUnitaryComplexSubtype m)

/-- Honest compactness target, ambient-image form:
the image of `SU(m)` inside the ambient matrix space should be compact. -/
def SpecialUnitaryCompactRangeTarget (m : ℕ) : Prop :=
  IsCompact
    (Set.range
      (fun U : SpecialUnitaryComplexSubtype m =>
        ((U : Matrix (Fin m) (Fin m) ℂ))))

/-- The subtype compactness target is just a definitional wrapper. -/
theorem specialUnitaryCompactSubtypeTarget_iff (m : ℕ) :
    SpecialUnitaryCompactSubtypeTarget m ↔
      CompactSpace (SpecialUnitaryComplexSubtype m) := by
  rfl

/-- The ambient-range compactness target is just a definitional wrapper. -/
theorem specialUnitaryCompactRangeTarget_iff (m : ℕ) :
    SpecialUnitaryCompactRangeTarget m ↔
      IsCompact
        (Set.range
          (fun U : SpecialUnitaryComplexSubtype m =>
            ((U : Matrix (Fin m) (Fin m) ℂ)))) := by
  rfl

/-- Sanity theorem: the topology assault is now pinned to the correct Mathlib
objects and no longer depends on guessed names. -/
theorem specialUnitaryCompact_namespace_recon_complete : True := by
  trivial

end ComplexTargets

end

end YangMills.ClayCore
