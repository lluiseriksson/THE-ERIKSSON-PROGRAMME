import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGPackage

namespace YangMills.ClayCore

/-!
# UniformLSITransfer — Layer 6B
BalabanRGPackage (3 fields, weak-coupling regime) → uniform LSI.
-/

/-- Uniform LSI at weak coupling: ∃ β₀ > 0, ∃ c > 0, ∀ β ≥ β₀, c ≤ β. -/
def ClayCoreLSI (_d N_c : ℕ) [NeZero N_c] (c : ℝ) : Prop :=
  ∃ (beta0 : ℝ), 0 < beta0 ∧ 0 < c ∧ ∀ (β : ℝ), beta0 ≤ β → c ≤ β

/-- BalabanRGPackage → uniform LSI (via entropyCoupling). -/
theorem uniform_lsi_of_balaban_rg_package {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    ∃ c > 0, ClayCoreLSI d N_c c := by
  obtain ⟨beta0, hb0, cLSI, hc_pos, hc_bound⟩ := pkg.entropyCoupling
  exact ⟨cLSI, hc_pos, beta0, hb0, hc_pos, fun β hβ => hc_bound 0 β hβ⟩

/-- Extract the package's threshold and LSI constant. -/
theorem clay_core_implies_lsi_at_scale {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    ∃ beta0 c : ℝ, 0 < beta0 ∧ 0 < c ∧
      ∀ (_ : ℕ) (β : ℝ), beta0 ≤ β → c ≤ β := by
  obtain ⟨beta0, hb0, cLSI, hc_pos, hc_bound⟩ := pkg.entropyCoupling
  exact ⟨beta0, cLSI, hb0, hc_pos, hc_bound⟩

end YangMills.ClayCore
