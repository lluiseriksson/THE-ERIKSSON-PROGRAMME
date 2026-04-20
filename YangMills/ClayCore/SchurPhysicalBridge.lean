/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.SchurZeroMean
import YangMills.ClayCore.SchurNormSquared

/-!
# Physical bridge: Schur L2.3 → ClayYangMillsPhysicalStrong chain

Defines the **fundamental observable** `F_fund(U) = Re(tr U)` on
`SU(N_c)` and exposes its two elementary properties used by the
physical-gap chain:

* `fundamentalObservable_mean_zero` — consumes L2.3
  (`sunHaarProb_trace_re_integral_zero`) and proves
  `∫ F_fund dHaar = 0` on `SU(N_c)` for `N_c ≥ 2`.

* `fundamentalObservable_bounded` — uniform pointwise bound
  `|F_fund(U)| ≤ N_c`, via the Mathlib entry-norm bound
  `entry_norm_bound_of_unitary`.

Together these two facts are precisely the input required by the
fundamental-representation side of the physical Wilson-loop chain in
`ClayYangMillsPhysicalStrong`: a class function on `SU(N_c)` that is
uniformly bounded and Haar-orthogonal to the trivial representation.

The `fundamentalObservable_ConnectedCorrDecay` link (showing that
`wilsonConnectedCorr` for `F_fund` obeys a genuine exponential cluster
bound) needs Haar-independence of distinct plaquette holonomies at
`β = 0` and is deferred: its proof would use L2.5 (Schur
orthogonality for matrix coefficients) together with finite-lattice
cluster expansion, neither of which is yet wired in.

Source: PETER_WEYL_ROADMAP.md — Layer 2 / Physical-chain wiring.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry.  No new axioms.
-/

namespace YangMills

open MeasureTheory Matrix Complex Finset

noncomputable section

/-- Fundamental-representation observable on `SU(N_c)`:
the real part of the trace of the group element. -/
noncomputable def fundamentalObservable (N_c : ℕ) [NeZero N_c] :
    ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ :=
  fun U => U.val.trace.re

/-- **Mean-zero bridge (L2.3 wiring).**

`∫ F_fund dHaar = 0` on `SU(N_c)` for `N_c ≥ 2`.

This is the first non-trivial dependency of the physical-gap chain
on Schur orthogonality: the real part of the fundamental character
integrates to zero against normalized Haar measure, which is the
orthogonality relation `⟨χ_fund, χ_triv⟩ = 0`. -/
theorem fundamentalObservable_mean_zero
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) :
    ∫ U, fundamentalObservable N_c U ∂(sunHaarProb N_c) = 0 := by
  unfold fundamentalObservable
  exact sunHaarProb_trace_re_integral_zero N_c hN

/-- **Uniform pointwise bound.**

`|F_fund(U)| ≤ N_c` for every `U ∈ SU(N_c)`.

Combining `|Re z| ≤ ‖z‖`, the triangle inequality for finite sums,
and `entry_norm_bound_of_unitary` gives the bound. -/
theorem fundamentalObservable_bounded
    (N_c : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :
    |fundamentalObservable N_c U| ≤ (N_c : ℝ) := by
  unfold fundamentalObservable
  have hU : U.val ∈ Matrix.unitaryGroup (Fin N_c) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.property).1
  have hre : |U.val.trace.re| ≤ ‖U.val.trace‖ :=
    Complex.abs_re_le_norm U.val.trace
  have htr : ‖U.val.trace‖ ≤ (N_c : ℝ) := by
    have heq : U.val.trace = ∑ i : Fin N_c, U.val i i := by
      simp [Matrix.trace, Matrix.diag_apply]
    rw [heq]
    calc ‖∑ i : Fin N_c, U.val i i‖
        ≤ ∑ i : Fin N_c, ‖U.val i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N_c, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => entry_norm_bound_of_unitary hU i i)
      _ = (N_c : ℝ) := by simp
  linarith

end

end YangMills
