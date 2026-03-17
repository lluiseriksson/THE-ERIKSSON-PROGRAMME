import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations

/-!
# M1b: CompactSpace for SU(N) — v0.8.35

Uses `entry_norm_bound_of_unitary` from Mathlib (RCLike API).
-/

namespace YangMills
open Matrix Set

noncomputable section
variable {N : ℕ} [NeZero N]

/-! ## entryBox is compact -/

private def entryBox (N : ℕ) : Set (Matrix (Fin N) (Fin N) ℂ) :=
  {A | ∀ i j, ‖A i j‖ ≤ 1}

private lemma isCompact_entryBox (N : ℕ) : IsCompact (entryBox N) := by
  have heq : entryBox N = Set.pi Set.univ (fun _ : Fin N =>
      Set.pi Set.univ (fun _ : Fin N => Metric.closedBall (0 : ℂ) 1)) := by
    ext A
    constructor
    · intro h i _ j _; simpa [Metric.mem_closedBall, dist_zero_right] using h i j
    · intro h i j; simpa [Metric.mem_closedBall, dist_zero_right] using h i (Set.mem_univ _) j (Set.mem_univ _)
  rw [heq]
  exact isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1

/-! ## SU(N) ⊆ entryBox — uses entry_norm_bound_of_unitary from Mathlib -/

private lemma specialUnitaryGroup_subset_entryBox :
    (↑(Matrix.specialUnitaryGroup (Fin N) ℂ) : Set (Matrix (Fin N) (Fin N) ℂ)) ⊆
    entryBox N := by
  intro A hA i j
  exact entry_norm_bound_of_unitary (mem_specialUnitaryGroup_iff.mp hA).1 i j

/-! ## SU(N) is closed -/

private lemma isClosed_unitaryGroup_set :
    IsClosed (↑(Matrix.unitaryGroup (Fin N) ℂ) :
      Set (Matrix (Fin N) (Fin N) ℂ)) := by
  change IsClosed (↑(unitary (Matrix (Fin N) (Fin N) ℂ)) :
    Set (Matrix (Fin N) (Fin N) ℂ))
  exact isClosed_unitary

private lemma isClosed_det_eq_one :
    IsClosed ({A : Matrix (Fin N) (Fin N) ℂ | A.det = 1}) :=
  isClosed_singleton.preimage (by fun_prop)

lemma isClosed_specialUnitaryGroup :
    IsClosed (↑(Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have heq : (↑(Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Set (Matrix (Fin N) (Fin N) ℂ)) =
      ↑(Matrix.unitaryGroup (Fin N) ℂ) ∩ {A | A.det = 1} := by
    ext A; constructor
    · intro hA; exact ⟨(mem_specialUnitaryGroup_iff.mp hA).1,
                        (mem_specialUnitaryGroup_iff.mp hA).2⟩
    · intro ⟨h1, h2⟩; exact mem_specialUnitaryGroup_iff.mpr ⟨h1, h2⟩
  rw [heq]
  exact isClosed_unitaryGroup_set.inter isClosed_det_eq_one

/-! ## CompactSpace -/

lemma isCompact_specialUnitaryGroup :
    IsCompact (↑(Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Set (Matrix (Fin N) (Fin N) ℂ)) :=
  (isCompact_entryBox N).of_isClosed_subset
    isClosed_specialUnitaryGroup
    specialUnitaryGroup_subset_entryBox

instance instCompactSpaceSUN_concrete (N : ℕ) [NeZero N] :
    CompactSpace ↥(Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  isCompact_iff_compactSpace.mp isCompact_specialUnitaryGroup

end
end YangMills
