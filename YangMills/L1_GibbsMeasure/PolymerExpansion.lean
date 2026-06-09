/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure

/-!
# Polymer representation, step 1 — the high-temperature expansion

The bridge from the lattice Gibbs theory to the verified Kotecký–Preiss
machinery begins with the **Mayer/high-temperature expansion** of the
Boltzmann weight: writing `exp(-β·E_p) = 1 + f_p` per plaquette,

  `exp(-β·S(A)) = ∏_p (1 + f_p(A)) = ∑_{S ⊆ plaquettes} ∏_{p∈S} f_p(A)`,

so the partition function is a **polymer-gas sum over plaquette sets**
(`partitionFunction_eq_sum_plaquetteSets`), with per-plaquette activities
bounded by `e^{|β|·B} − 1` for bounded plaquette energy
(`abs_plaquetteWeight_le`) — small at small `β`, which is exactly the
smallness the KP criterion consumes downstream.

This is step 1 of the polymer representation
(`docs/DEPENDENCY-GRAPH.md` §4 item 4).  Step 2 (grouping plaquette sets
into connected polymers and matching `PolymerSystem`/`KPCriterion`) is the
next campaign.  No character theory (T4) is needed on this route.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory GaugeConfig

attribute [local instance] FiniteLatticeGeometry.fintypeP

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

/-- The **Mayer weight** of a plaquette: `f_p(A) = exp(-β·E(hol_p A)) − 1`.
These are the polymer-gas activities of the high-temperature expansion. -/
noncomputable def plaquetteWeight (pe : G → ℝ) (β : ℝ)
    (A : GaugeConfig d N G)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) : ℝ :=
  Real.exp (-β * pe (plaquetteHolonomy A p)) - 1

/-- **The high-temperature expansion of the Boltzmann weight:**
`exp(-β·S(A)) = ∑_{S ⊆ plaquettes} ∏_{p∈S} f_p(A)`. -/
theorem boltzmann_eq_sum_plaquetteSets (pe : G → ℝ) (β : ℝ)
    (A : GaugeConfig d N G) :
    Real.exp (-β * wilsonAction pe A)
      = ∑ S ∈ (Finset.univ :
          Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset,
          ∏ p ∈ S, plaquetteWeight pe β A p := by
  classical
  unfold wilsonAction
  rw [show -β * (∑ p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G),
      pe (plaquetteHolonomy A p))
      = ∑ p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G),
        (-β * pe (plaquetteHolonomy A p)) from Finset.mul_sum _ _ _]
  rw [Real.exp_sum]
  have hfac : ∀ p ∈ (Finset.univ :
      Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))),
      Real.exp (-β * pe (plaquetteHolonomy A p))
        = plaquetteWeight pe β A p + 1 := by
    intro p _
    unfold plaquetteWeight
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_add]
  exact Finset.sum_congr rfl fun t _ => by
    rw [Finset.prod_const_one, mul_one]

/-- **The partition function as a polymer-gas sum:** integrating the
high-temperature expansion termwise (under explicit integrability of each
finite product — automatic for bounded energies). -/
theorem partitionFunction_eq_sum_plaquetteSets [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (pe : G → ℝ) (β : ℝ)
    (hint : ∀ S ∈ (Finset.univ :
        Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset,
      Integrable (fun A : GaugeConfig d N G => ∏ p ∈ S, plaquetteWeight pe β A p)
        (gaugeMeasureFrom (d := d) (N := N) μ)) :
    partitionFunction (d := d) (N := N) μ pe β
      = ∑ S ∈ (Finset.univ :
          Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset,
          ∫ A, ∏ p ∈ S, plaquetteWeight pe β A p
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  unfold partitionFunction
  rw [show (fun U : GaugeConfig d N G => Real.exp (-β * wilsonAction pe U))
      = fun U => ∑ S ∈ (Finset.univ :
          Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset,
          ∏ p ∈ S, plaquetteWeight pe β U p from
    funext fun U => boltzmann_eq_sum_plaquetteSets pe β U]
  exact MeasureTheory.integral_finset_sum _ hint

/-- `|e^t − 1| ≤ e^{|t|} − 1` (the two-sided exponential bound). -/
private lemma abs_exp_sub_one_le_exp_abs (t : ℝ) :
    |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg
      (by linarith [Real.one_le_exp ht] : (0 : ℝ) ≤ Real.exp t - 1)]
  · rw [abs_of_neg ht, abs_of_nonpos
      (by linarith [Real.exp_lt_one_iff.mpr ht] : Real.exp t - 1 ≤ 0)]
    have h1 := Real.add_one_le_exp t
    have h2 := Real.add_one_le_exp (-t)
    linarith

/-- **Activity smallness:** for plaquette energy bounded by `B`, every Mayer
weight is bounded by `e^{|β|·B} − 1` — uniformly small at small coupling.
This is the seed of the KP smallness criterion for the plaquette polymer
gas. -/
theorem abs_plaquetteWeight_le (pe : G → ℝ) (β : ℝ)
    (A : GaugeConfig d N G)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G))
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) :
    |plaquetteWeight pe β A p| ≤ Real.exp (|β| * B) - 1 := by
  unfold plaquetteWeight
  refine le_trans (abs_exp_sub_one_le_exp_abs _) ?_
  have h1 : |(-β) * pe (plaquetteHolonomy A p)| ≤ |β| * B := by
    rw [abs_mul, abs_neg]
    have hB : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hpe 1)
    exact mul_le_mul_of_nonneg_left (hpe _) (abs_nonneg β)
  have h2 : Real.exp |(-β) * pe (plaquetteHolonomy A p)|
      ≤ Real.exp (|β| * B) := Real.exp_le_exp.mpr h1
  have h3 : -β * pe (plaquetteHolonomy A p)
      = (-β) * pe (plaquetteHolonomy A p) := by ring
  rw [h3]
  linarith

end YangMills
