import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.DivMod
import Lean.Elab.Tactic.NormCast

/-! PRE-VALIDATION: source present, .olean not materialized, not compiler-verified.
Minimal casting/injectivity check only, not an operator dictionary. -/

namespace YangMills.RG

def neumannFiniteSiteIntegerCoordinates {d N : ℕ} (x : Fin d → Fin N) : Fin d → ℤ :=
  fun mu => ((x mu).val : ℤ)

theorem neumannFiniteSiteIntegerCoordinates_injective {d N : ℕ} :
    Function.Injective (neumannFiniteSiteIntegerCoordinates (d := d) (N := N)) := by
  intro x y h
  funext mu
  apply Fin.ext
  have he := congrFun h mu
  change ((x mu).val : ℤ) = ((y mu).val : ℤ) at he
  exact_mod_cast he

theorem neumannOwnerCastRepro (n M depth : ℕ) :
    ((n / M ^ depth : ℕ) : ℤ) = (n : ℤ) / ((M ^ depth : ℕ) : ℤ) := by
  exact Int.natCast_ediv n (M ^ depth)

theorem neumannFiniteOwnerEqualityRepro {d N : ℕ} (x y : Fin d → Fin N) :
    x = y ↔ neumannFiniteSiteIntegerCoordinates x = neumannFiniteSiteIntegerCoordinates y := by
  exact (neumannFiniteSiteIntegerCoordinates_injective (d := d) (N := N)).eq_iff.symm

end YangMills.RG

#print axioms YangMills.RG.neumannFiniteSiteIntegerCoordinates_injective
#print axioms YangMills.RG.neumannOwnerCastRepro
#print axioms YangMills.RG.neumannFiniteOwnerEqualityRepro
