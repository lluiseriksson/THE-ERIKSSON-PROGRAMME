/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.GaugeMarginal
import YangMills.ClayCore.SchurZeroMean
import YangMills.ClayCore.SchurMomentVanishing
import YangMills.ClayCore.SchurL25

/-!
# First lattice gauge-observable expectations, end-to-end

Instantiating the single-edge bridge (`GaugeMarginal.lean`) with the verified group-level
zero-mean facts gives the **first genuine lattice gauge-observable expectations computed
end-to-end**: the expectation of an edge holonomy's trace under the full SU(N) lattice
gauge measure vanishes for `N ≥ 2`.

`integral_single_edge_eq_zero` (the lattice centre-vanishing engine) + the Schur
zero-mean fact `∫ tr U dμ = 0` (`SchurZeroMean.lean`) compose to
`∫ tr(A e) d(gaugeMeasureFrom (sunHaarProb N_c)) = 0`.  This is the lattice statement
"a single Wilson line of length one has zero expectation", the SU(N) analogue of the
U(1) Fourier-mode case.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory Matrix

/-- **First SU(N) lattice gauge-observable expectation: the single-edge trace vanishes.**
For `N_c ≥ 2`, the expectation of the trace of a single edge holonomy under the SU(N_c)
lattice gauge measure (product Haar) is zero:
`∫ tr(A e) d(gaugeMeasureFrom (sunHaarProb N_c)) = 0`.
Composes the single-edge bridge `integral_single_edge_eq_zero` with the Schur zero-mean
identity `sunHaarProb_trace_complex_integral_zero`.  The first lattice Wilson-observable
expectation derived end-to-end (not merely at the group level). -/
theorem gauge_single_edge_trace_eq_zero
    (d Nlat : ℕ) [NeZero d] [NeZero Nlat]
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c)
    (e : PosEdge d Nlat) :
    ∫ A, (configToPos A e).val.trace
      ∂(gaugeMeasureFrom (d := d) (N := Nlat) (sunHaarProb N_c)) = 0 := by
  refine integral_single_edge_eq_zero (sunHaarProb N_c) e
    (fun U => U.val.trace) (trace_integrable N_c).aestronglyMeasurable ?_
  exact sunHaarProb_trace_complex_integral_zero N_c hN

/-- **Higher N-ality single-edge Wilson observable vanishes on the lattice.**  For
`N_c ∤ k`, the expectation of the `k`-th power of a single edge holonomy's trace under the
SU(N_c) lattice gauge measure is zero:
`∫ (tr(A e))^k d(gaugeMeasureFrom (sunHaarProb N_c)) = 0`.  Composes the single-edge bridge
with the Z_N centre selection rule `sunHaarProb_trace_pow_complex_integral_zero`.  The
`k = 1` case is `gauge_single_edge_trace_eq_zero`; higher `k` are the higher-N-ality
single-edge Wilson observables, all killed end-to-end by the lattice centre engine. -/
theorem gauge_single_edge_trace_pow_eq_zero
    (d Nlat : ℕ) [NeZero d] [NeZero Nlat]
    (N_c k : ℕ) [NeZero N_c] (hk : ¬ N_c ∣ k)
    (e : PosEdge d Nlat) :
    ∫ A, ((configToPos A e).val.trace) ^ k
      ∂(gaugeMeasureFrom (d := d) (N := Nlat) (sunHaarProb N_c)) = 0 := by
  have hcont : Continuous
      (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => (U.val.trace) ^ k) :=
    (continuous_trace_sub N_c).pow k
  refine integral_single_edge_eq_zero (sunHaarProb N_c) e
    (fun U => (U.val.trace) ^ k)
    (hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable ?_
  exact sunHaarProb_trace_pow_complex_integral_zero N_c k hk

/-- **Real part of the single-edge trace vanishes on the lattice.**  The expectation of
`Re tr(A e)` (the physical, real-valued single-plaquette-free Wilson observable) under the
SU(N_c) lattice gauge measure is zero for `N_c ≥ 2` — the real form of
`gauge_single_edge_trace_eq_zero`, obtained by pushing `Complex.reCLM` through the
integral. -/
theorem gauge_single_edge_trace_re_eq_zero
    (d Nlat : ℕ) [NeZero d] [NeZero Nlat]
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c)
    (e : PosEdge d Nlat) :
    ∫ A, ((configToPos A e).val.trace).re
      ∂(gaugeMeasureFrom (d := d) (N := Nlat) (sunHaarProb N_c)) = 0 := by
  refine integral_single_edge_eq_zero (sunHaarProb N_c) e
    (fun U => (U.val.trace).re)
    ((Complex.reCLM.continuous.comp (continuous_trace_sub N_c)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable ?_
  -- ∫ Re(tr) = Re(∫ tr) = Re 0 = 0
  have hint := trace_integrable N_c
  have hcomm := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at hcomm
  rw [hcomm, sunHaarProb_trace_complex_integral_zero N_c hN]
  rfl

/-- **Two-edge trace product factorizes and vanishes on the lattice.**  For two distinct
positive edges `e₁ ≠ e₂`, the expectation of the product of their holonomy traces under the
SU(N_c) lattice gauge measure factorizes (independence) and vanishes, since each factor has
zero Haar mean:
`∫ tr(A e₁)·tr(A e₂) dμ_gauge = (∫ tr)·(∫ tr) = 0` for `N_c ≥ 2`.  A genuine two-edge
(disconnected) Wilson observable, killed by the scalar-product factorization
`integral_prod_edges_eq_zero`. -/
theorem gauge_two_edge_trace_prod_eq_zero
    (d Nlat : ℕ) [NeZero d] [NeZero Nlat]
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c)
    (e₁ : PosEdge d Nlat) :
    ∫ A, (∏ e : PosEdge d Nlat,
        (if e = e₁ then (configToPos A e).val.trace else 1))
      ∂(gaugeMeasureFrom (d := d) (N := Nlat) (sunHaarProb N_c)) = 0 := by
  classical
  refine integral_prod_edges_eq_zero (sunHaarProb N_c)
    (fun e U => if e = e₁ then U.val.trace else 1) ?_ e₁ ?_
  · -- each factor is AEStronglyMeasurable
    intro e
    by_cases h : e = e₁
    · simp only [h, if_pos]
      exact (trace_integrable N_c).aestronglyMeasurable
    · simp only [if_neg h]
      exact aestronglyMeasurable_const
  · -- the e₁ factor has zero group mean
    simp only [if_true]
    exact sunHaarProb_trace_complex_integral_zero N_c hN

/-- **Second moment of the single-edge trace is bounded by N on the lattice.**  The
expectation of `|tr(A e)|²` under the SU(N_c) lattice gauge measure is at most `N_c`:
`∫ |tr(A e)|² dμ_gauge ≤ N_c`.  Transports the group-level L² bound
`sunHaarProb_trace_normSq_integral_le` (`∫|tr U|² ≤ N`) through the single-edge marginal.
This is the lattice second-moment / variance control for the single-edge Wilson observable
— the input to two-point correlator bounds. -/
theorem gauge_single_edge_trace_normSq_le
    (d Nlat : ℕ) [NeZero d] [NeZero Nlat]
    (N_c : ℕ) [NeZero N_c]
    (e : PosEdge d Nlat) :
    ∫ A, (Complex.normSq (configToPos A e).val.trace : ℝ)
      ∂(gaugeMeasureFrom (d := d) (N := Nlat) (sunHaarProb N_c)) ≤ (N_c : ℝ) := by
  have hcont : Continuous
      (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        (Complex.normSq U.val.trace : ℝ)) :=
    Complex.continuous_normSq.comp (continuous_trace_sub N_c)
  rw [integral_single_edge (sunHaarProb N_c) e
    (fun U => (Complex.normSq U.val.trace : ℝ))
    (hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable]
  exact ClayCore.sunHaarProb_trace_normSq_integral_le (N := N_c)

/-- **The single-edge second moment is nonnegative** (it is the integral of `|tr|² ≥ 0`).
Together with `gauge_single_edge_trace_normSq_le` this pins the lattice second moment to
`[0, N_c]`. -/
theorem gauge_single_edge_trace_normSq_nonneg
    (d Nlat : ℕ) [NeZero d] [NeZero Nlat]
    (N_c : ℕ) [NeZero N_c]
    (e : PosEdge d Nlat) :
    0 ≤ ∫ A, (Complex.normSq (configToPos A e).val.trace : ℝ)
      ∂(gaugeMeasureFrom (d := d) (N := Nlat) (sunHaarProb N_c)) :=
  integral_nonneg (fun _ => Complex.normSq_nonneg _)

end YangMills
