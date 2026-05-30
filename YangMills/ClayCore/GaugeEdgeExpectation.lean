/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.GaugeMarginal
import YangMills.ClayCore.SchurZeroMean
import YangMills.ClayCore.SchurMomentVanishing

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

end YangMills
