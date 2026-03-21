import Mathlib
import YangMills.ClayCore.BalabanRG.SpecialUnitaryCompact

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# SpecialUnitaryCompactReduction — Layer topology-reduction

Honest reduction layer for the topological assault on `SU(n)`.

This file does not prove compactness yet.
Instead, it reduces the problem to two concrete obligations phrased directly in
the ambient matrix coordinates:

* closedness of the special-unitary range,
* entrywise boundedness of that range.

This avoids premature dependence on the ambient `Bornology` API in the current
Mathlib snapshot, while still isolating exactly the Heine–Borel style gap that
must be discharged next.
-/

noncomputable section

/-- The ambient subset corresponding to `SU(m)` inside the matrix space. -/
abbrev specialUnitarySet (m : ℕ) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  Set.range (fun U : SpecialUnitaryComplexSubtype m =>
    ((U : Matrix (Fin m) (Fin m) ℂ)))

/-- Closedness target for the ambient `SU(m)` subset. -/
def SpecialUnitaryClosedTarget (m : ℕ) : Prop :=
  IsClosed (specialUnitarySet m)

/-- Entrywise boundedness target for the ambient `SU(m)` subset. -/
def SpecialUnitaryEntrywiseBoundedTarget (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ U ∈ specialUnitarySet m, ∀ i j, ‖U i j‖ ≤ C

/-- Honest witness object for the remaining topological gap. -/
structure SpecialUnitaryClosedEntrywiseBoundedWitness (m : ℕ) where
  closed_range : SpecialUnitaryClosedTarget m
  bounded_range : SpecialUnitaryEntrywiseBoundedTarget m

/-- Exact remaining topological bridge:
closedness plus entrywise boundedness of the ambient `SU(m)` range should imply
compactness. -/
structure SpecialUnitaryClosedEntrywiseBoundedToCompactTransfer (m : ℕ) where
  transfer :
    SpecialUnitaryClosedTarget m →
    SpecialUnitaryEntrywiseBoundedTarget m →
    SpecialUnitaryCompactRangeTarget m

/-- A transfer plus a concrete witness close the ambient compactness target. -/
theorem specialUnitaryCompactRangeTarget_of_closed_entrywise_bounded
    (m : ℕ)
    (tr : SpecialUnitaryClosedEntrywiseBoundedToCompactTransfer m)
    (hclosed : SpecialUnitaryClosedTarget m)
    (hbounded : SpecialUnitaryEntrywiseBoundedTarget m) :
    SpecialUnitaryCompactRangeTarget m := by
  exact tr.transfer hclosed hbounded

/-- A transfer plus a bundled witness close the ambient compactness target. -/
theorem specialUnitaryCompactRangeTarget_of_witness
    (m : ℕ)
    (tr : SpecialUnitaryClosedEntrywiseBoundedToCompactTransfer m)
    (wit : SpecialUnitaryClosedEntrywiseBoundedWitness m) :
    SpecialUnitaryCompactRangeTarget m := by
  exact specialUnitaryCompactRangeTarget_of_closed_entrywise_bounded
    m tr wit.closed_range wit.bounded_range

/-- Registry theorem:
the topology assault on `SU(m)` is now reduced to an explicit Heine–Borel style
transfer together with a concrete closed+entrywise-bounded witness. -/
theorem specialUnitary_topology_gap_reduced
    (m : ℕ)
    (tr : SpecialUnitaryClosedEntrywiseBoundedToCompactTransfer m) :
    (∃ wit : SpecialUnitaryClosedEntrywiseBoundedWitness m, True) →
      SpecialUnitaryCompactRangeTarget m := by
  intro h
  rcases h with ⟨wit, _⟩
  exact specialUnitaryCompactRangeTarget_of_witness m tr wit

end

end YangMills.ClayCore
