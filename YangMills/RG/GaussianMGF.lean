/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Gaussian field-size / MGF bound from a covariance bound (gauge-RG, `hRpoly` substrate)

`docs/BALABAN-SOURCE-BOUNDS.md`.  The Bałaban small-field fluctuation integral
needs one Gaussian fact: a Gaussian fluctuation field with **bounded
covariance** has uniformly bounded exponential moments.  This file proves the
finite-dimensional moment-generating-function bound that consumes the
covariance/Schur bounds of `RG/KernelSchur.lean` / `RG/CovarianceKernel.lean`.

* **`gaussian_exp_integral_le`** — if the 1-D marginal of a centered measure
  `μ` under the linear observable `L` is the real Gaussian `gaussianReal 0 v`
  (the defining marginal property of a centered Gaussian field), and the
  variance `v ≤ B` (with `B = a·S·‖L‖²` the value
  `expDecay_quadratic_form_le` / `psd_cauchy_schwarz` supplies), then
  `∫ exp(L φ) dμ ≤ exp(B/2)`.  Built directly on Mathlib's `mgf_gaussianReal`.

**Honest scope.**  The hypothesis `μ.map L = gaussianReal 0 v` is the genuine
centered-1-D-marginal property of a Gaussian field — a faithful carried
hypothesis (true for every Gaussian measure), **not** a fabricated Gaussian
constructor.  Deriving it from an abstract `[IsGaussian μ]` (centered) is the
natural follow-on.  This does NOT prove `hRpoly`; it is the Gaussian
fluctuation-bound toolkit that the gauge construction consumes.

**Source.**  Standard Gaussian MGF (Mathlib `mgf_gaussianReal`); the
application is Bałaban CMP 95/109's small-field integral; strategy/framing
Lluis Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace YangMills.RG

/-- **Gaussian field-size (MGF) bound from a covariance bound.**  If the 1-D
marginal of a centered measure `μ` under the linear observable `L` is the real
Gaussian `gaussianReal 0 v`, and the variance `v` is bounded by `B` (the value
the covariance/Schur bound supplies, `B = a·S·‖L‖²`), then the exponential
field-size integral is bounded: `∫ exp(L φ) dμ ≤ exp(B/2)`.  A Gaussian
fluctuation field with bounded covariance has uniformly bounded exponential
moments — the small-field fluctuation-integral input. -/
theorem gaussian_exp_integral_le {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {L : E → ℝ} {v : NNReal} {B : ℝ}
    (hL : μ.map L = gaussianReal 0 v) (hv : (v : ℝ) ≤ B) :
    ∫ x, Real.exp (L x) ∂μ ≤ Real.exp (B / 2) := by
  have hmgf : mgf L μ 1 = ∫ x, Real.exp (L x) ∂μ := by
    unfold ProbabilityTheory.mgf; simp
  rw [← hmgf, mgf_gaussianReal hL 1]
  apply Real.exp_le_exp.mpr
  have he : (0 : ℝ) * 1 + (v : ℝ) * 1 ^ 2 / 2 = (v : ℝ) / 2 := by ring
  rw [he]
  linarith

end YangMills.RG
