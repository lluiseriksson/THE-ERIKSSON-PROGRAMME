import Mathlib.Data.Fintype.Basic

def branchRepro (full : Bool) : Type :=
  match full with
  | true => Unit
  | false => Bool

instance branchReproFintype (full : Bool) : Fintype (branchRepro full) := by
  cases full
  · change Fintype Bool
    exact inferInstance
  · change Fintype Unit
    exact inferInstance

theorem branchRepro_unique (x y : branchRepro true) : x = y := by
  change Unit at x y
  exact Subsingleton.elim x y

#print axioms branchRepro_unique
