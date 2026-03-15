import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations

/-!
# M1b: CompactSpace for SU(N)

Proves `CompactSpace ↥(Matrix.specialUnitaryGroup (Fin N) ℂ)` concretely,
replacing the axiom `instCompactSpaceSUN` in `SUN_StateConstruction.lean`.

## Proof strategy

  SU(N) ⊆ {A | ∀ i j, ‖A i j‖ ≤ 1}    [entry_norm_bound_of_unitary]
         = ∏ᵢ ∏ⱼ closedBall 0 1          [Pi type = Matrix]
         is compact                        [isCompact_univ_pi + isCompact_closedBall]
  SU(N) is closed:
    U(N) is closed                         [isClosed_unitary]
    {det = 1} is closed                   [fun_prop + isClosed_singleton.preimage]
    SU(N) = U(N) ∩ {det = 1}             [definition]
  closed ⊆ compact → compact              [IsCompact.of_isClosed_subset]
  IsCompact (carrier) ↔ CompactSpace      [isCompact_iff_compactSpace]
-/

namespace YangMills

open Matrix Set

noncomputable section

variable {N : ℕ} [NeZero N]

/-! ## Step 1: Pi-of-balls is compact -/

/-- The "entry box": all matrices whose entries lie in the closed unit disk. -/
private def entryBox (N : ℕ) : Set (Matrix (Fin N) (Fin N) ℂ) :=
  {A | ∀ i j, A i j ∈ Metric.closedBall (0 : ℂ) 1}

/-- The entry box is compact (finite product of compact sets). -/
private lemma isCompact_entryBox (N : ℕ) : IsCompact (entryBox N) := by
  have : entryBox N = Set.pi Set.univ
      (fun _ : Fin N => Set.pi Set.univ
        (fun _ : Fin N => Metric.closedBall (0 : ℂ) 1)) := by
    ext A; simp [entryBox, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]
  rw [this]
  exact isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1

/-! ## Step 2: unitaryGroup ⊆ entryBox -/

/-- Every entry of a unitary matrix has norm ≤ 1. -/
private lemma unitaryGroup_subset_entryBox :
    (↑(Matrix.unitaryGroup (Fin N) ℂ) : Set (Matrix (Fin N) (Fin N) ℂ)) ⊆
    entryBox N := fun A hA i j => by
  simp [entryBox, Metric.mem_closedBall, dist_zero_right]
  exact entry_norm_bound_of_unitary hA i j

/-- specialUnitaryGroup ⊆ unitaryGroup ⊆ entryBox -/
private lemma specialUnitaryGroup_subset_entryBox :
    (↑(Matrix.specialUnitaryGroup (Fin N) ℂ) : Set (Matrix (Fin N) (Fin N) ℂ)) ⊆
    entryBox N := by
  intro A hA
  apply unitaryGroup_subset_entryBox
  -- specialUnitaryGroup = unitaryGroup ⊓ ker(det)
  exact (Matrix.mem_specialUnitaryGroup_iff.mp hA).1

/-! ## Step 3: specialUnitaryGroup is closed -/

/-- The unitary group is closed in the matrix space. -/
private lemma isClosed_unitaryGroup_SUN :
    IsClosed (↑(Matrix.unitaryGroup (Fin N) ℂ) :
      Set (Matrix (Fin N) (Fin N) ℂ)) := by
  change IsClosed (↑(unitary (Matrix (Fin N) (Fin N) ℂ)) :
    Set (Matrix (Fin N) (Fin N) ℂ))
  exact isClosed_unitary

/-- The set {det = 1} is closed (det is continuous by fun_prop). -/
private lemma isClosed_det_eq_one :
    IsClosed {A : Matrix (Fin N) (Fin N) ℂ | A.det = 1} :=
  isClosed_singleton.preimage (by fun_prop)

/-- SU(N) is closed in the matrix space. -/
lemma isClosed_specialUnitaryGroup :
    IsClosed (↑(Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have hmem : (↑(Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Set (Matrix (Fin N) (Fin N) ℂ)) =
      ↑(Matrix.unitaryGroup (Fin N) ℂ) ∩
      {A | A.det = 1} := by
    ext A
    simp [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    tauto
  rw [hmem]
  exact isClosed_unitaryGroup_SUN.inter isClosed_det_eq_one

/-! ## Step 4: IsCompact → CompactSpace -/

/-- The carrier set of SU(N) is compact. -/
lemma isCompact_specialUnitaryGroup :
    IsCompact (↑(Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Set (Matrix (Fin N) (Fin N) ℂ)) :=
  IsCompact.of_isClosed_subset
    (isCompact_entryBox N)
    isClosed_specialUnitaryGroup
    specialUnitaryGroup_subset_entryBox

/-- SU(N) is a compact topological space.
    This replaces the axiom `instCompactSpaceSUN` in SUN_StateConstruction.lean. -/
instance instCompactSpaceSUN_concrete (N : ℕ) [NeZero N] :
    CompactSpace ↥(Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  isCompact_iff_compactSpace.mp isCompact_specialUnitaryGroup

end

end YangMills
