import Mathlib
import YangMills.ClayCore.BalabanRG.SpecialUnitaryEntrywiseBounded

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open Matrix

/-!
# SpecialUnitaryClosed — Layer topology-closed

This file closes the closedness half of the honest compactness reduction for the
local special-unitary range.

Strategy:
* identify `specialUnitarySet m` with the concrete subset
  `{A | A ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ A.det = 1}`,
* prove the unitary condition is closed as an equality set
  `A * star A = 1`,
* prove the determinant-one condition is closed by continuity of determinant,
* combine both closed conditions by intersection.

Together with `SpecialUnitaryEntrywiseBounded`, this closes the honest local
closed+bounded package for `SU(m)`. The final compactness step still uses the
explicit transfer object from `SpecialUnitaryCompactReduction`.
-/

noncomputable section

/-- Concrete closed-set model for the local special-unitary range. -/
def specialUnitaryClosedCandidate (m : ℕ) :
    Set (Matrix (Fin m) (Fin m) ℂ) :=
  {A | A ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ A.det = 1}

/-- The ambient range used by the program is exactly the concrete special-unitary
cut inside the matrix space. -/
theorem specialUnitarySet_eq_closedCandidate
    (m : ℕ) :
    specialUnitarySet m = specialUnitaryClosedCandidate m := by
  ext A
  constructor
  · intro hA
    rcases hA with ⟨U, rfl⟩
    simp [specialUnitaryClosedCandidate]
  · intro hA
    rcases hA with ⟨hU, hdet⟩
    refine ⟨⟨A, ?_⟩, rfl⟩
    simpa [Matrix.mem_specialUnitaryGroup_iff] using ⟨hU, hdet⟩

/-- The unitary condition cuts out a closed subset of the ambient matrix space. -/
theorem isClosed_unitary_condition
    (m : ℕ) :
    IsClosed {A : Matrix (Fin m) (Fin m) ℂ |
      A ∈ Matrix.unitaryGroup (Fin m) ℂ} := by
  have hEq :
      IsClosed {A : Matrix (Fin m) (Fin m) ℂ |
        A * star A = (1 : Matrix (Fin m) (Fin m) ℂ)} := by
    exact isClosed_eq (by fun_prop) continuous_const
  simpa [Matrix.mem_unitaryGroup_iff] using hEq

/-- The determinant-one condition is closed in the ambient matrix space. -/
theorem isClosed_det_eq_one
    (m : ℕ) :
    IsClosed {A : Matrix (Fin m) (Fin m) ℂ | A.det = (1 : ℂ)} := by
  have hdet :
      Continuous (fun A : Matrix (Fin m) (Fin m) ℂ => A.det) := by
    simpa using
      (Continuous.matrix_det
        (n := Fin m)
        (R := ℂ)
        (A := fun A : Matrix (Fin m) (Fin m) ℂ => A)
        continuous_id)
  exact isClosed_eq hdet continuous_const

/-- Closedness of the ambient local `SU(m)` range. -/
theorem specialUnitary_closed_target
    (m : ℕ) :
    SpecialUnitaryClosedTarget m := by
  rw [SpecialUnitaryClosedTarget, specialUnitarySet_eq_closedCandidate]
  unfold specialUnitaryClosedCandidate
  simpa [Set.setOf_and] using
    (isClosed_unitary_condition m).inter (isClosed_det_eq_one m)

/-- Honest witness bundling the closed and entrywise-bounded halves for the
local `SU(m)` compactness target. -/
def specialUnitary_closed_entrywise_bounded_witness
    (m : ℕ) :
    SpecialUnitaryClosedEntrywiseBoundedWitness m where
  closed_range := specialUnitary_closed_target m
  bounded_range := specialUnitary_entrywise_bounded_target m

/-- The local `SU(m)` compactness target follows once the explicit reduction
transfer is supplied. -/
theorem specialUnitary_compact_range_target_internal
    (m : ℕ)
    (tr : SpecialUnitaryClosedEntrywiseBoundedToCompactTransfer m) :
    SpecialUnitaryCompactRangeTarget m := by
  exact specialUnitaryCompactRangeTarget_of_witness
    m tr (specialUnitary_closed_entrywise_bounded_witness m)

/-- Registry theorem: the two honest topological halves are now fully proved
inside the repo. -/
theorem specialUnitary_topology_gap_closed_internal
    (m : ℕ) :
    SpecialUnitaryClosedTarget m ∧
      SpecialUnitaryEntrywiseBoundedTarget m := by
  exact ⟨specialUnitary_closed_target m, specialUnitary_entrywise_bounded_target m⟩

/-- With the explicit reduction transfer, the local compactness target is also
recovered. -/
theorem specialUnitary_topology_gap_closed_to_compact
    (m : ℕ)
    (tr : SpecialUnitaryClosedEntrywiseBoundedToCompactTransfer m) :
    SpecialUnitaryClosedTarget m ∧
      SpecialUnitaryEntrywiseBoundedTarget m ∧
      SpecialUnitaryCompactRangeTarget m := by
  refine ⟨specialUnitary_closed_target m, specialUnitary_entrywise_bounded_target m, ?_⟩
  exact specialUnitary_compact_range_target_internal m tr

end

end YangMills.ClayCore
