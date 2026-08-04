/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinRectangleVolume

/-!
# D-7 — thermodynamic limit from Dobrushin comparison

This file closes the whole-sequence Cauchy step for a local Ising observable.
The input observable lives on one fixed centred rectangle.  Every finite-volume
term is its canonical lift to a larger free rectangle.  The only small-coupling
hypothesis is the visible Dobrushin window
`2 * tanh |β| + 2 * tanh |γ| ≤ α < 1`.

No Cauchy, convergence, boundary-tail, or infinite-volume premise is assumed.
-/

namespace YangMills.OS

namespace Dobrushin

open Filter Topology

/-- The whole finite-volume sequence attached to one fixed local observable.
The `n`-th term uses the free square of radius `r+n`. -/
noncomputable def centeredLocalGibbsExpectation
    (β γ : ℝ) (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ)
    (n : ℕ) : ℝ :=
  expect (gibbsMu (isingWeight
      (rectJ (L := 2 * (r + n) + 1) (T := 2 * (r + n) + 1) β γ)))
    (liftCenteredObservable (Nat.le_add_right r n) g)

/-- Comparable radii satisfy the explicit Dobrushin Cauchy estimate. -/
theorem dist_centeredLocalGibbsExpectation_le
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ)
    {n m : ℕ} (hnm : n ≤ m) :
    dist (centeredLocalGibbsExpectation β γ r g n)
        (centeredLocalGibbsExpectation β γ r g m) ≤
      α ^ n *
        (((Fintype.card (CenteredRect r) : ℝ) * osc g) / (1 - α)) := by
  have hcmp := centered_local_observable_comparison β γ α hα0 hα1 hwin
    (r := r) (n := r + n) (m := r + m)
    (Nat.le_add_right r n) (by omega) g
  rw [show r + n - r = n by omega] at hcmp
  change
    |centeredLocalGibbsExpectation β γ r g n -
      centeredLocalGibbsExpectation β γ r g m| ≤ _
  rw [abs_sub_comm]
  calc
    |centeredLocalGibbsExpectation β γ r g m -
        centeredLocalGibbsExpectation β γ r g n|
        ≤ (α ^ n / (1 - α)) *
            ((Fintype.card (CenteredRect r) : ℝ) * osc g) := hcmp
    _ = α ^ n *
        (((Fintype.card (CenteredRect r) : ℝ) * osc g) / (1 - α)) := by
      ring

/-- **Whole-sequence Cauchy theorem in the Dobrushin window.** -/
theorem cauchySeq_centeredLocalGibbsExpectation
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ) :
    CauchySeq (centeredLocalGibbsExpectation β γ r g) := by
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  let M : ℝ := ((Fintype.card (CenteredRect r) : ℝ) * osc g) / (1 - α)
  have hpow : Tendsto (fun n : ℕ => α ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1
  have hlim : Tendsto (fun n : ℕ => α ^ n * M) atTop (𝓝 0) := by
    simpa using hpow.mul_const M
  have hev : ∀ᶠ n in atTop, α ^ n * M < δ :=
    (tendsto_order.1 hlim).2 δ hδ
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, ?_⟩
  intro n hn m hm
  rcases le_total n m with hnm | hmn
  · exact (dist_centeredLocalGibbsExpectation_le β γ α hα0 hα1 hwin
      r g hnm).trans_lt (by simpa [M] using hN n hn)
  · rw [dist_comm]
    exact (dist_centeredLocalGibbsExpectation_le β γ α hα0 hα1 hwin
      r g hmn).trans_lt (by simpa [M] using hN m hm)

/-- The infinite-volume value selected from completeness of `ℝ`. -/
noncomputable def infiniteCenteredLocalGibbsExpectation
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ) : ℝ :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (cauchySeq_centeredLocalGibbsExpectation β γ α hα0 hα1 hwin r g))

/-- The entire finite-volume sequence converges to the constructed value. -/
theorem tendsto_infiniteCenteredLocalGibbsExpectation
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ) :
    Tendsto (centeredLocalGibbsExpectation β γ r g) atTop
      (𝓝 (infiniteCenteredLocalGibbsExpectation
        β γ α hα0 hα1 hwin r g)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (cauchySeq_centeredLocalGibbsExpectation β γ α hα0 hα1 hwin r g))

end Dobrushin

end YangMills.OS
