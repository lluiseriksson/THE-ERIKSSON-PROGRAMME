/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure

/-!
# Single-edge marginal of the product gauge measure

The lattice gauge measure `gaugeMeasureFrom μ` (`L1_GibbsMeasure/GibbsMeasure.lean`) is
the product Haar measure on gauge configurations, expressed in positive-edge coordinates
as `(Measure.pi fun _ : PosEdge => μ).map gaugeConfigEquiv`.

This file proves its **single-edge marginal**: pushing `gaugeMeasureFrom μ` forward along
"evaluate the configuration at a fixed positive edge `e`" returns `μ` itself.  For a
probability measure `μ`, the other factors integrate to `1`, so each edge variable is
distributed exactly as `μ` — the first statement here about a genuine *gauge observable*
(an edge holonomy), and the measure-theoretic basis for reducing single-edge Wilson-line
expectations to a one-group Haar integral (e.g. `∫ ⟨open line⟩ = 0` via the centre engine).

Proof: `configToPos` is `gaugeConfigEquiv.symm`, so `eval e ∘ configToPos` is
`Function.eval e` on the product, and `Measure.map` composes; Mathlib's
`measurePreserving_eval` gives the product marginal `= μ`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-- **Single-edge marginal of the product gauge measure.**  Evaluating a gauge
configuration at a fixed positive edge `e` pushes `gaugeMeasureFrom μ` forward to `μ`:
each edge variable carries the Haar law `μ`.  (For a probability measure the remaining
edge factors integrate to `1`.) -/
theorem gaugeMeasureFrom_map_eval (μ : Measure G) [IsProbabilityMeasure μ]
    (e : PosEdge d N) :
    (gaugeMeasureFrom (d := d) (N := N) μ).map (fun A => configToPos A e) = μ := by
  classical
  -- `gaugeMeasureFrom μ = (Measure.pi _).map gaugeConfigEquiv`; compose the maps.
  unfold gaugeMeasureFrom
  -- measurability of `A ↦ configToPos A e = (gaugeConfigEquiv.symm A) e = eval e ∘ symm`
  have hsymm : Measurable (gaugeConfigEquiv (d := d) (N := N) (G := G)).symm := by
    rw [measurable_iff_comap_le]
    exact le_of_eq rfl
  have hmeas : Measurable (fun A : GaugeConfig d N G => configToPos A e) := by
    have h1 : (fun A : GaugeConfig d N G => configToPos A e)
        = (Function.eval e) ∘ gaugeConfigEquiv.symm := by
      funext A; rfl
    rw [h1]
    exact (measurable_pi_apply e).comp hsymm
  rw [Measure.map_map hmeas measurable_gaugeConfigEquiv]
  -- `(fun A => configToPos A e) ∘ gaugeConfigEquiv = Function.eval e`
  have hcomp : (fun A => configToPos A e) ∘ (gaugeConfigEquiv (d := d) (N := N) (G := G))
      = Function.eval e := by
    funext f
    show gaugeConfigEquiv.symm (gaugeConfigEquiv f) e = f e
    rw [Equiv.symm_apply_apply]
  rw [hcomp]
  exact (measurePreserving_eval (μ := fun _ : PosEdge d N => μ) e).map_eq

/-- **Single-edge observable reduces to a one-group integral.**  For any observable `f`
of a single edge holonomy, its expectation under the product gauge measure equals the
Haar integral of `f` over the group: `∫ f(A e) dμ_gauge = ∫ f dμ`.  This is the bridge
that turns a lattice gauge expectation of a one-edge observable into a single-group Haar
integral — where the centre-vanishing engine (`∫ χ dμ = 0` for non-trivial characters)
applies.  Proved by `integral_map` over the single-edge marginal. -/
theorem integral_single_edge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) [IsProbabilityMeasure μ] (e : PosEdge d N)
    (f : G → E) (hf : AEStronglyMeasurable f μ) :
    ∫ A, f (configToPos A e) ∂(gaugeMeasureFrom (d := d) (N := N) μ) = ∫ g, f g ∂μ := by
  classical
  have hmeas : AEMeasurable (fun A : GaugeConfig d N G => configToPos A e)
      (gaugeMeasureFrom (d := d) (N := N) μ) := by
    have hsymm : Measurable (gaugeConfigEquiv (d := d) (N := N) (G := G)).symm := by
      rw [measurable_iff_comap_le]; exact le_of_eq rfl
    exact ((measurable_pi_apply e).comp hsymm).aemeasurable
  have hf' : AEStronglyMeasurable f
      ((gaugeMeasureFrom (d := d) (N := N) μ).map (fun A => configToPos A e)) := by
    rw [gaugeMeasureFrom_map_eval]; exact hf
  rw [← integral_map hmeas hf', gaugeMeasureFrom_map_eval]

end YangMills
