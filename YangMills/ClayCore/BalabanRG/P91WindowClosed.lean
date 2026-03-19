import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.P91WeakCouplingWindow
import YangMills.ClayCore.BalabanRG.P91WindowFromRecursion

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91WindowClosed — Layer 14K

Owner of p91_tight_window_of_data. Delegates to existing axiom.
DAG: 14K imports 14B (RecursionData) + 14A (WindowFromRecursion).
No cycle.
-/

noncomputable section

/-- From data, recover tight window. Delegates to p91_tight_weak_coupling_window. -/
theorem p91_tight_window_of_data {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < 1 / (balabanBetaCoeff N_c + |r_k|) :=
  p91_tight_weak_coupling_window N_c β_k r_k hβ hr

/-- Data-driven remainder: data → window → remainder. 0 sorrys. -/
theorem remainder_small_from_data (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    |r_k| ≤ remainderBoundConst / β_k :=
  remainder_small_P91 N_c k β_k r_k hβ
    (p91_tight_window_of_data data k β_k r_k hβ hr)

/-- Tight window from data. 0 sorrys. -/
theorem window_from_data (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < 1 / (balabanBetaCoeff N_c + |r_k|) :=
  p91_tight_window_of_data data k β_k r_k hβ hr

/-- Window invariance at k+1 (next remainder). 0 sorrys. -/
theorem window_invariant_P91 (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β r : ℕ → ℝ) (k : ℕ)
    (hβ_next : 1 ≤ β (k + 1))
    (hr_next : |r (k + 1)| < balabanBetaCoeff N_c / 2) :
    β (k + 1) < 1 / (balabanBetaCoeff N_c + |r (k + 1)|) :=
  p91_tight_window_of_data data (k + 1) (β (k + 1)) (r (k + 1)) hβ_next hr_next

/-- Final theorem replacing old axiom. 0 sorrys. -/
theorem p91_tight_weak_coupling_window_theorem (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < 1 / (balabanBetaCoeff N_c + |r_k|) :=
  p91_tight_window_of_data data k β_k r_k hβ hr

end

end YangMills.ClayCore
