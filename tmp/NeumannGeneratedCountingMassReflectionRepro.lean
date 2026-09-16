import YangMills.RG.NeumannHalfCellBlockReflection

/-!
PRE-VALIDATION: source present, no repro .olean materialized; not compiler
verified. Isolate the exact dependent box cast and injective if-congruence
before compiling the generated physical tower. No physical result is claimed.
-/

namespace YangMills.RG

theorem neumannCountingReflection_cast_repro {d A B : ℕ} (h : A = B)
    (branch : Fin d → Bool) (x : FinBox d A) :
    Equiv.cast (congrArg (FinBox d) h) (neumannHalfCellReflection branch x) =
      neumannHalfCellReflection branch (Equiv.cast (congrArg (FinBox d) h) x) := by
  subst B
  rfl

theorem neumannCountingReflection_if_repro {d N : ℕ} {V : Type*}
    (branch : Fin d → Bool) (x y : FinBox d N) (a b : V) :
    (if neumannHalfCellReflection branch x = neumannHalfCellReflection branch y
      then a else b) = (if x = y then a else b) := by
  exact if_congr (neumannHalfCellReflection_involutive branch).injective.eq_iff rfl rfl

end YangMills.RG

#print axioms YangMills.RG.neumannCountingReflection_cast_repro
#print axioms YangMills.RG.neumannCountingReflection_if_repro
