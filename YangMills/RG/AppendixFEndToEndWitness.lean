/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpCardTilt

/-!
# Appendix-F B1--B3 end-to-end non-vacuity witness

This module closes P3.5 brick B4 of the `hRpoly` campaign.  On the minimal
one-dimensional one-site torus, with no holes, it instantiates the B1 witness
rate, the B2 bounded-hole input, and the B3 residual-to-KP bridge with a
literally constant, strictly nonzero activity.

The amplitude is chosen at the exact remaining scalar KP margin

`A = 1 - exp (-1)`.

Since the unique nonempty polymer is a singleton, its modified metric is zero
and the constant activity `A * exp (-rate)` saturates the residual profile.
Thus the final KP criterion has a jointly satisfiable, nonzero instance.

Honest scope: this is a non-vacuity seal for the conditional B1--B3 lane.  It
does not identify the witness activity with a Yang--Mills fluctuation integral
and therefore does not prove the raw `hRpoly` estimate.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

namespace AppendixFEndToEndWitness

/-- The unique cube of the `d = 1`, `L = 1` torus. -/
def cube : Cube 1 1 := fun _ => 0

/-- Every cube of the minimal torus is the chosen cube. -/
lemma cube_eq (x : Cube 1 1) : x = cube := by
  funext i
  exact Subsingleton.elim _ _

/-- Every nonempty cube finset on the minimal torus is the singleton. -/
lemma finset_eq_singleton (X : Finset (Cube 1 1)) (hX : X.Nonempty) :
    X = {cube} := by
  ext x
  constructor
  · intro _
    simp [cube_eq x]
  · intro hx
    have hc : cube ∈ X := by
      obtain ⟨y, hy⟩ := hX
      simpa [cube_eq y] using hy
    simpa [Finset.mem_singleton.mp hx] using hc

/-- The empty hole family used by the witness. -/
def holes : HoleFamily 1 1 := ⟨∅⟩

/-- B1's explicit witness rate in dimension one. -/
noncomputable def kappa0 : ℝ := appendixFWitnessKappa0 1

/-- The B2 cardinality tilt with no holes. -/
def theta : ℝ := boundedHoleCardinalityTilt 1 0

/-- The shifted residual rate consumed by B3. -/
noncomputable def rate : ℝ :=
  polymerClusterResidualRate (4 * kappa0 + 3 + theta) kappa0

/-- The exact B1 geometric factor. -/
noncomputable def geometricFactor : ℝ :=
  ((3 ^ 1 : ℕ) : ℝ) ^ 2 * (Real.exp (-kappa0) * 2 ^ (3 ^ 1 + 1))

/-- The positive amplitude left by the scalar KP margin. -/
noncomputable def amplitude : ℝ := 1 - geometricFactor

/-- A literally constant activity on all cube finsets.  On the unique active
polymer it is the residual exponential profile at the witness rate. -/
noncomputable def activity (_X : Finset (Cube 1 1)) : ℂ :=
  ((amplitude * Real.exp (-rate) : ℝ) : ℂ)

lemma geometricFactor_eq : geometricFactor = Real.exp (-1) := by
  simpa [geometricFactor, kappa0] using appendixFWitnessKappa0_geometric_eq 1

lemma geometricFactor_lt_one : geometricFactor < 1 := by
  simpa [geometricFactor, kappa0] using appendixFWitnessKappa0_geometric_lt_one 1

lemma amplitude_pos : 0 < amplitude := by
  unfold amplitude
  linarith [geometricFactor_lt_one]

lemma rate_pos : 0 < rate := by
  have hk : 0 < kappa0 := by
    simpa [kappa0] using appendixFWitnessKappa0_pos 1
  have ht : theta = 1 := by norm_num [theta, boundedHoleCardinalityTilt]
  rw [show rate = kappa0 + theta by
    unfold rate
    unfold polymerClusterResidualRate
    ring]
  rw [ht]
  linarith

/-- The witness singleton is an active polymer for the constant activity. -/
noncomputable def polymer : OmegaPolymerType holes activity := by
  refine ⟨{cube}, ?_, ?_, ?_, ?_⟩
  · simp
  · intro x hx y hy
    rw [Finset.mem_singleton] at hx hy
    subst x y
    exact ⟨SimpleGraph.Walk.nil, fun v hv => by
      simpa [SimpleGraph.Walk.support] using hv⟩
  · simp [polymerWithHoles, holes]
  · simp [skeleton, holes]

lemma activity_nonzero :
    (omegaHolePolymerSystem holes activity).activity polymer ≠ 0 := by
  change ((amplitude * Real.exp (-rate) : ℝ) : ℂ) ≠ 0
  exact_mod_cast mul_ne_zero (ne_of_gt amplitude_pos) (Real.exp_ne_zero (-rate))

lemma polymer_metric_zero : discreteModifiedMetric holes polymer.val = 0 := by
  apply discreteModifiedMetric_singleton_skeleton holes polymer.val
    polymer.property.2.1 cube
  simp [polymer, skeleton, holes]

lemma residual_bound (Y : OmegaPolymerType holes activity) :
    ‖activity Y.val‖ ≤
      amplitude * appendixFHoleExpWeight holes rate Y.val := by
  have hY : Y.val = {cube} := finset_eq_singleton Y.val Y.property.1
  have hmetric : discreteModifiedMetric holes {cube} = 0 := polymer_metric_zero
  rw [hY]
  change ‖((amplitude * Real.exp (-rate) : ℝ) : ℂ)‖ ≤
    amplitude * appendixFHoleExpWeight holes rate {cube}
  rw [show appendixFHoleExpWeight holes rate {cube} = Real.exp (-rate) by
    simp [appendixFHoleExpWeight, hmetric]]
  have hnonneg : 0 ≤ amplitude * Real.exp (-rate) :=
    mul_nonneg (le_of_lt amplitude_pos) (Real.exp_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]

lemma scalar_smallness :
    amplitude * (1 - geometricFactor)⁻¹ ≤ 1 := by
  have hne : 1 - geometricFactor ≠ 0 := ne_of_gt amplitude_pos
  rw [show amplitude = 1 - geometricFactor by rfl, mul_inv_cancel₀ hne]

end AppendixFEndToEndWitness

open AppendixFEndToEndWitness

/-- **P3.5--B4 closure: a nonzero end-to-end B1--B3 instance.**

There is a concrete hole family and a literally constant activity on the
minimal torus for which the activity is nonzero and the final volume-uniform
active-skeleton KP criterion holds at B1's explicit rate. -/
theorem appendixF_endToEnd_nonzero_witness :
    ∃ (HF : HoleFamily 1 1) (zH : Finset (Cube 1 1) → ℂ),
      (∃ Y : OmegaPolymerType HF zH,
        (omegaHolePolymerSystem HF zH).activity Y ≠ 0) ∧
      KP.KPCriterion
        ((omegaHolePolymerSystem HF zH).scaleActivity (Real.exp 0))
        (fun Y => (Y.val.card : ℝ)) := by
  refine ⟨holes, activity, ⟨polymer, activity_nonzero⟩, ?_⟩
  apply omegaHolePolymerSystem_KPCriterion_of_Hsharp_residual_bounded_holes
    holes activity 0 kappa0 0 amplitude amplitude
  · simp [holes]
  · simp [noEdgesBetweenHoles, holes]
  · simp [holes]
  · simp [holes]
  · exact le_of_lt amplitude_pos
  · exact le_of_lt amplitude_pos
  · simp
  · intro Y
    simpa [rate, theta, boundedHoleCardinalityTilt] using residual_bound Y
  · simpa [geometricFactor, kappa0] using appendixFWitnessKappa0_geometric_lt_one 1
  · simpa [amplitude, geometricFactor, kappa0] using scalar_smallness

end YangMills.RG
