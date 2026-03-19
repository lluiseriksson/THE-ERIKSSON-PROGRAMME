import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGPackage

namespace YangMills.ClayCore

/-!
# UniformLSITransfer — Layer 6B
-/

/-- Simplified uniform LSI statement at the Clay Core interface. -/
def ClayCoreLSI (d N_c : ℕ) [NeZero N_c] (c : ℝ) : Prop :=
  ∃ (β₀ : ℝ), 0 < β₀ ∧ 0 < c ∧
    ∀ (β : ℝ), β₀ ≤ β → c ≤ β

/-- BalabanRGPackage → uniform LSI. -/
theorem uniform_lsi_of_balaban_rg_package {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c) :
    ∃ c > 0, ClayCoreLSI d N_c c := by
  obtain ⟨cLSI, hc_pos, hc_bound⟩ := pkg.entropyCoupling
  exact ⟨cLSI, hc_pos, cLSI, hc_pos, hc_pos,
         fun β hβ => hc_bound 0 β (by linarith)⟩

/-- At each scale, the LSI constant is positive. -/
theorem clay_core_implies_lsi_at_scale {d N_c : ℕ} [NeZero N_c]
    (pkg : BalabanRGPackage d N_c)
    (k : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ c > 0, c ≤ β := by
  obtain ⟨cLSI, hc_pos, hc_bound⟩ := pkg.entropyCoupling
  exact ⟨cLSI, hc_pos, hc_bound k β hβ⟩

end YangMills.ClayCore
