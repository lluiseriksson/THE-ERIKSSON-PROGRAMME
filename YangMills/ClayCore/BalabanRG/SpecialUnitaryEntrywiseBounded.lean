import Mathlib
import YangMills.ClayCore.BalabanRG.SpecialUnitaryCompactReduction

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# SpecialUnitaryEntrywiseBounded — Layer topology-entrywise

This file closes the entrywise-bounded half of the honest compactness reduction
for the local special-unitary range.

The proof is completely honest and local:
every entry of a unitary matrix has norm at most `1`, and the special-unitary
group is a subgroup of the unitary group.

So the remaining topological gap is reduced to the closedness of the ambient
`SU(m)` range.
-/

noncomputable section

/-- The ambient `SU(m)` range is entrywise bounded, uniformly by the constant
`1`. -/
theorem specialUnitary_entrywise_bounded_target
    (m : ℕ) :
    SpecialUnitaryEntrywiseBoundedTarget m := by
  refine ⟨1, by positivity, ?_⟩
  intro U hU i j
  rcases hU with ⟨V, rfl⟩
  have hunitary :
      ((V : Matrix (Fin m) (Fin m) ℂ)) ∈ Matrix.unitaryGroup (Fin m) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup V.2
  simpa using entry_norm_bound_of_unitary hunitary i j

/-- Convenience corollary exposing the explicit constant `1`. -/
theorem specialUnitary_entrywise_norm_le_one
    (m : ℕ) :
    ∀ U ∈ specialUnitarySet m, ∀ i j, ‖U i j‖ ≤ (1 : ℝ) := by
  intro U hU i j
  rcases hU with ⟨V, rfl⟩
  have hunitary :
      ((V : Matrix (Fin m) (Fin m) ℂ)) ∈ Matrix.unitaryGroup (Fin m) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup V.2
  simpa using entry_norm_bound_of_unitary hunitary i j

end

end YangMills.ClayCore
