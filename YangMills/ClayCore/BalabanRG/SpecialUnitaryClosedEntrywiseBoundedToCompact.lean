import Mathlib
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import YangMills.ClayCore.BalabanRG.SpecialUnitaryClosed

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open Matrix
open Bornology

noncomputable section

abbrev SpecialUnitaryAmbient (m : ℕ) := Matrix (Fin m) (Fin m) ℂ

local instance instNormedAddCommGroupSpecialUnitaryAmbient (m : ℕ) :
    NormedAddCommGroup (SpecialUnitaryAmbient m) :=
  Matrix.linftyOpNormedAddCommGroup

local instance instNormedSpaceSpecialUnitaryAmbient (m : ℕ) :
    NormedSpace ℂ (SpecialUnitaryAmbient m) :=
  Matrix.linftyOpNormedSpace

/-- Entrywise boundedness implies bornological boundedness in the ambient matrix
space with the `linfty` matrix norm. -/
theorem specialUnitary_bornology_bounded_of_entrywise_bounded
    (m : ℕ)
    (hbounded : SpecialUnitaryEntrywiseBoundedTarget m) :
    Bornology.IsBounded (specialUnitarySet m) := by
  rcases hbounded with ⟨C, hC0, hC⟩
  refine
    ((isBounded_iff_forall_norm_le
      (E := SpecialUnitaryAmbient m) (s := specialUnitarySet m))).2 ?_
  refine ⟨(m : ℝ) * C, ?_⟩
  intro A hA
  let Cnn : NNReal := ⟨C, hC0⟩
  have hsup :
      (Finset.univ.sup fun i : Fin m => ∑ j : Fin m, ‖A i j‖₊) ≤ (m : NNReal) * Cnn := by
    refine Finset.sup_le ?_
    intro i hi
    calc
      ∑ j : Fin m, ‖A i j‖₊ ≤ ∑ j : Fin m, Cnn := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact_mod_cast (hC A hA i j)
      _ = (m : NNReal) * Cnn := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp [Fintype.card_fin]
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast hsup

/-- Honest compactness closure in the finite-dimensional ambient matrix space. -/
theorem specialUnitary_compact_range_target_of_closed_entrywise_bounded_honest
    (m : ℕ)
    (hclosed : SpecialUnitaryClosedTarget m)
    (hbounded : SpecialUnitaryEntrywiseBoundedTarget m) :
    SpecialUnitaryCompactRangeTarget m := by
  haveI : FiniteDimensional ℂ (SpecialUnitaryAmbient m) := by
    infer_instance
  haveI : ProperSpace (SpecialUnitaryAmbient m) :=
    FiniteDimensional.proper ℂ (SpecialUnitaryAmbient m)
  have hborn : Bornology.IsBounded (specialUnitarySet m) :=
    specialUnitary_bornology_bounded_of_entrywise_bounded m hbounded
  simpa [SpecialUnitaryCompactRangeTarget] using
    (Metric.isCompact_iff_isClosed_bounded (s := specialUnitarySet m)).2
      ⟨hclosed, hborn⟩

/-- The isolated topological transfer is now supplied internally. -/
def specialUnitary_closed_entrywise_bounded_to_compact_transfer
    (m : ℕ) :
    SpecialUnitaryClosedEntrywiseBoundedToCompactTransfer m := by
  refine ⟨?_⟩
  intro hclosed hbounded
  exact
    specialUnitary_compact_range_target_of_closed_entrywise_bounded_honest
      m hclosed hbounded

/-- Unconditional local compactness target for the ambient `SU(m)` range. -/
theorem specialUnitary_compact_range_target_unconditional
    (m : ℕ) :
    SpecialUnitaryCompactRangeTarget m := by
  exact specialUnitaryCompactRangeTarget_of_closed_entrywise_bounded
    m
    (specialUnitary_closed_entrywise_bounded_to_compact_transfer m)
    (specialUnitary_closed_target m)
    (specialUnitary_entrywise_bounded_target m)

/-- Registry theorem: the local topological compactness target is now closed
without any external transfer input. -/
theorem specialUnitary_topology_gap_closed_unconditional
    (m : ℕ) :
    SpecialUnitaryClosedTarget m ∧
      SpecialUnitaryEntrywiseBoundedTarget m ∧
      SpecialUnitaryCompactRangeTarget m := by
  refine ⟨specialUnitary_closed_target m, specialUnitary_entrywise_bounded_target m, ?_⟩
  exact specialUnitary_compact_range_target_unconditional m

end

end YangMills.ClayCore
