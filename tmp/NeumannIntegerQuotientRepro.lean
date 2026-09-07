import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! PRE-VALIDATION: Mathlib-only quotient repro, not compiler-verified. -/
namespace YangMills.RG
noncomputable section

theorem neumannZeroResidue_exists_integerQuotient
    (d N : ℕ) (u : Fin d → ℤ)
    (hu : (fun i => (u i : ZMod N)) = (0 : (Fin d → ZMod N))) :
    ∃ v : Fin d → ℤ, ∀ i, u i = (N : ℤ) * v i := by
  have hd : ∀ i, (N : ℤ) ∣ u i := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (u i) N).mp
    exact congrFun hu i
  choose v hv using hd
  exact ⟨v, hv⟩

theorem neumannIntegerQuotient_phase
    (d N : ℕ) [NeZero N] (z : Fin d → ℂ) (u v : Fin d → ℤ)
    (hv : ∀ i, u i = (N : ℤ) * v i) :
    (∑ i, Complex.I * z i * (u i : ℂ) / (N : ℂ)) =
      Complex.I * (∑ i, z i * (v i : ℂ)) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hv i, Int.cast_mul, Int.cast_natCast]
  field_simp <;> ring

theorem neumannIntegerQuotient_zero_iff
    (d N : ℕ) [NeZero N] (u v : Fin d → ℤ)
    (hv : ∀ i, u i = (N : ℤ) * v i) : u = 0 ↔ v = 0 := by
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  constructor
  · intro hu
    funext i
    have hmul : (N : ℤ) * v i = 0 := by
      rw [← hv i, hu]
      rfl
    exact (mul_eq_zero.mp hmul).resolve_left hN
  · intro hz
    funext i
    rw [hv i, hz]
    simp

end
end YangMills.RG

#print axioms YangMills.RG.neumannZeroResidue_exists_integerQuotient
#print axioms YangMills.RG.neumannIntegerQuotient_phase
#print axioms YangMills.RG.neumannIntegerQuotient_zero_iff
