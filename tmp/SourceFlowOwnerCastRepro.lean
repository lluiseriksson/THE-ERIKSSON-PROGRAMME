import Mathlib.Data.Fin.Basic

/-!
# PRE-VALIDATION: Mathlib-only finite-box size-cast repro

Source present; .olean not materialized; result not compiler-verified.
No project imports; run before the physical owner dictionary draft.
-/

example {d A B : ℕ} (h : A = B) (x : Fin d → Fin A) (i : Fin d) :
    ((h ▸ x : Fin d → Fin B) i).val = (x i).val := by
  cases h
  rfl

example {d A B : ℕ} (h : A = B) (x : Fin d → Fin A) (i : Fin d) :
    ((Equiv.cast (congrArg (fun n => Fin d → Fin n) h) x) i).val = (x i).val := by
  cases h
  rfl
