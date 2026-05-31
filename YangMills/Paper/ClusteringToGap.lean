/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.Paper.MassGapAssembly
import YangMills.KP.Convergence

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

/-- **Strong-coupling lattice mass gap (M3) — full conditional assembly.**
Putting the pieces together: given
* an **infrared geometric cluster bound** `|covIR d| ≤ C₁·rᵈ` with `0 < r < 1` (the output
  of the Kotecký–Preiss expansion / Appendix A, carried as a hypothesis), and
* a **UV suppression bound** `|covUV| ≤ C₂·exp(-(c₀·t))` (the §6.3 single-scale bound),
* with the correlator decomposing as `cov = covIR t + covUV` (telescoping, §6.1),

the full connected correlator decays **exponentially with a strictly positive rate**
`min(m*, c₀) > 0`, where `m* = -log r > 0` is the mass extracted from the cluster ratio.
This is the honest **strong-coupling lattice** mass-gap statement (Osterwalder–Seiler) — the
rung beneath Clay.  It is conditional on the cluster bound and UV bound as explicit
hypotheses (never axioms); the Clay prize additionally needs the continuum limit + OS
axioms, which are open and untouched here. -/
theorem lattice_mass_gap_of_clustering
    (covIR : ℕ → ℝ) (covUV C1 C2 r c0 : ℝ) (t : ℕ)
    (hr0 : 0 < r) (hr1 : r < 1) (hc0 : 0 < c0)
    (hIRbound : ∀ d, |covIR d| ≤ C1 * r ^ d)
    (hUV : |covUV| ≤ C2 * Real.exp (-(c0 * (t : ℝ)))) :
    ∃ gap : ℝ, 0 < gap ∧
      |covIR t + covUV| ≤ (C1 + C2) * Real.exp (-(gap * (t : ℝ))) := by
  obtain ⟨mstar, hmpos, hIR⟩ :=
    clustering_gives_exponential_decay covIR C1 r hr0 hr1 hIRbound
  refine ⟨min mstar c0, lt_min hmpos hc0, ?_⟩
  exact Paper.mass_gap_bound (covIR t + covUV) (covIR t) covUV C1 C2 mstar c0 (t : ℝ)
    (Nat.cast_nonneg t) rfl (hIR t) hUV

/-! ### Finite susceptibility — the summed correlator converges

Exponential clustering has a physical corollary: the **susceptibility**
`χ = ∑_d |cov d|` (the integrated correlator) is *finite*.  A diverging susceptibility is
the hallmark of a *massless* phase, so finiteness is the quantitative face of the mass gap.
These reuse the geometric-series back-half (`KP.Convergence`). -/

/-- **Finite susceptibility: the summed correlator converges.**  Under a geometric cluster
bound `|cov d| ≤ C·rᵈ` (`0 ≤ r < 1`), the integrated correlator `∑_d |cov d|` is summable.
Finiteness of the susceptibility is the quantitative signature of the mass gap (a massless
phase has divergent susceptibility). -/
theorem susceptibility_summable
    (cov : ℕ → ℝ) (C r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ d, |cov d| ≤ C * r ^ d) :
    Summable (fun d => |cov d|) :=
  KP.cluster_series_summable (fun d => |cov d|) C r hr0 hr1
    (fun d => abs_nonneg _) hbound

/-- **Susceptibility bound: `χ ≤ C/(1−r)`.**  The integrated correlator is bounded by the
closed-form geometric tail, giving an explicit finite susceptibility from the cluster
bound. -/
theorem susceptibility_le
    (cov : ℕ → ℝ) (C r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ d, |cov d| ≤ C * r ^ d) :
    ∑' d, |cov d| ≤ C / (1 - r) :=
  KP.cluster_sum_le (fun d => |cov d|) C r hr0 hr1
    (fun d => abs_nonneg _) hbound

/-- The susceptibility is nonnegative (it is a sum of absolute values). -/
theorem susceptibility_nonneg (cov : ℕ → ℝ) :
    0 ≤ ∑' d, |cov d| :=
  tsum_nonneg (fun d => abs_nonneg _)

end YangMills
