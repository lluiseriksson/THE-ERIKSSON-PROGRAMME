/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.Paper.MassGapAssembly

/-!
# Clustering ⟹ exponential decay ⟹ mass-gap rate (the M3 bridge)

This is the honest **strong-coupling lattice** step toward the prize (milestone M3,
Osterwalder–Seiler).  It is *not* the Clay problem — that requires the continuum limit and
OS/Wightman axioms, which remain open mathematics — but it is the real rung beneath it:
turning a geometric cluster bound (the conclusion of the Kotecký–Preiss expansion,
`YangMills/KP/`, and Appendix A of the paper) into the exponential correlator decay that
`mass_gap_bound` (§7) consumes.

The chain, all with the hard analytic input carried as an **explicit hypothesis** (never an
axiom): a connected-correlator cluster bound `|cov d| ≤ C·r^d` with `0 ≤ r < 1` yields
exponential decay `|cov d| ≤ C·exp(-(m*)·d)` with a *strictly positive* mass `m* = -log r`,
which is exactly the IR clustering hypothesis of `mass_gap_bound`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open Real

/-- **Geometric ratio as an exponential rate.**  For `0 < r < 1`, `r = exp(-(m*))` with the
strictly positive mass `m* = -log r > 0`.  This is the elementary fact that a geometric
decay ratio *is* an exponential rate, and that the rate is positive precisely because
`r < 1`. -/
theorem geometric_ratio_eq_exp_neg {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    r = Real.exp (-(-Real.log r)) ∧ 0 < -Real.log r := by
  refine ⟨?_, ?_⟩
  · rw [neg_neg, Real.exp_log hr0]
  · exact neg_pos.mpr (Real.log_neg hr0 hr1)

/-- **A geometric cluster bound is exponential decay with positive mass.**  If the
connected correlator at separation `d` obeys `|cov d| ≤ C·r^d` with `0 ≤ r < 1`, then
`|cov d| ≤ C·exp(-(m*)·d)` with the strictly positive mass `m* = -log r`.  This is the
content of "exponential clustering ⇒ mass gap" at fixed (strong) coupling: the cluster
ratio `r` *is* `exp(-m*)`, so the geometric bound is literally exponential decay.  The
cluster bound itself is the hypothesis (supplied, in the full program, by the KP expansion
/ Appendix A). -/
theorem clustering_gives_exponential_decay
    (cov : ℕ → ℝ) (C r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hbound : ∀ d, |cov d| ≤ C * r ^ d) :
    ∃ mstar : ℝ, 0 < mstar ∧ ∀ d : ℕ, |cov d| ≤ C * Real.exp (-(mstar * d)) := by
  refine ⟨-Real.log r, neg_pos.mpr (Real.log_neg hr0 hr1), fun d => ?_⟩
  have hrew : r ^ d = Real.exp (-(-Real.log r * d)) := by
    have hpos : (0 : ℝ) < r ^ d := pow_pos hr0 d
    rw [show -(-Real.log r * d) = Real.log (r ^ d) by rw [Real.log_pow]; ring,
        Real.exp_log hpos]
  have hb := hbound d
  rw [hrew] at hb
  exact hb

/-- **M3 IR-clustering input, ready for `mass_gap_bound`.**  Specializing
`clustering_gives_exponential_decay` to a fixed separation `t = d`, the cluster bound at
that separation is exactly the IR hypothesis `|covIR| ≤ C₁·exp(-(m*)·t)` of
`mass_gap_bound`.  This is the connector that lets the KP cluster bound discharge the §5
hypothesis of the §7 mass-gap assembly — the strong-coupling lattice gap, conditional only
on the (imported, hypothesis-carried) cluster bound. -/
theorem clustering_to_massGap_IR
    (cov : ℕ → ℝ) (C r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hbound : ∀ d, |cov d| ≤ C * r ^ d) (d : ℕ) :
    ∃ mstar : ℝ, 0 < mstar ∧ |cov d| ≤ C * Real.exp (-(mstar * (d : ℝ))) := by
  obtain ⟨mstar, hpos, hdecay⟩ := clustering_gives_exponential_decay cov C r hr0 hr1 hbound
  exact ⟨mstar, hpos, hdecay d⟩

end YangMills
