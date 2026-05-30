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

/-- **Zero-mean single-edge observables have zero gauge expectation.**  If an observable
`f` has vanishing Haar mean `∫ f dμ = 0`, then its expectation under the full lattice
gauge measure also vanishes.  This is the lattice realization of the centre-vanishing
engine: an edge observable whose group integral is zero (e.g. a non-trivial U(1) Fourier
mode `fourier k`, `k ≠ 0`, or `tr U` on SU(N), both already proved to integrate to zero)
contributes zero to every lattice gauge expectation.  The first lattice gauge-observable
expectation computed end-to-end. -/
theorem integral_single_edge_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) [IsProbabilityMeasure μ] (e : PosEdge d N)
    (f : G → E) (hf : AEStronglyMeasurable f μ) (hmean : ∫ g, f g ∂μ = 0) :
    ∫ A, f (configToPos A e) ∂(gaugeMeasureFrom (d := d) (N := N) μ) = 0 := by
  rw [integral_single_edge μ e f hf, hmean]

/-- **Product observable over all positive edges factorizes.**  For a `𝕜`-valued
observable assigned to each positive edge, the expectation of the product over all edges
under the product gauge measure factorizes into the per-edge group integrals:
`∫ ∏ₑ fₑ(A e) dμ_gauge = ∏ₑ ∫ fₑ dμ`.  This is the gauge-measure form of Fubini
(`integral_fintype_prod_eq_prod`) transported through the positive-edge coordinates;
it is the basis for evaluating multi-edge Wilson observables on the lattice. -/
theorem integral_prod_edges {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure G) [IsProbabilityMeasure μ] (f : PosEdge d N → G → 𝕜)
    (hf : ∀ e, AEStronglyMeasurable (f e) μ) :
    ∫ A, ∏ e : PosEdge d N, f e (configToPos A e)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ∏ e : PosEdge d N, ∫ g, f e g ∂μ := by
  classical
  -- Transport along `gaugeConfigEquiv`: `configToPos A e = (symm A) e`, then Fubini.
  unfold gaugeMeasureFrom
  have hmeas : Measurable (gaugeConfigEquiv (d := d) (N := N) (G := G)) :=
    measurable_gaugeConfigEquiv
  have hsymm : Measurable (gaugeConfigEquiv (d := d) (N := N) (G := G)).symm := by
    rw [measurable_iff_comap_le]; exact le_of_eq rfl
  rw [integral_map hmeas.aemeasurable]
  · have hcongr : (fun x : PosEdge d N → G =>
        ∏ e : PosEdge d N, f e (configToPos (gaugeConfigEquiv x) e))
        = (fun x : PosEdge d N → G => ∏ e : PosEdge d N, f e (x e)) := by
      funext x
      refine Finset.prod_congr rfl (fun e _ => ?_)
      rw [show configToPos (gaugeConfigEquiv x) e = x e from
        congrFun (gaugeConfigEquiv.left_inv x) e]
    rw [hcongr]
    exact integral_fintype_prod_eq_prod (fun (_ : PosEdge d N) => f _)
  · -- the integrand on the mapped measure is AEStronglyMeasurable; rewrite product of
    -- functions, then apply the Finset product lemma edge-by-edge.
    have hfun : (fun A : GaugeConfig d N G => ∏ e : PosEdge d N, f e (configToPos A e))
        = ∏ e : PosEdge d N, (fun A : GaugeConfig d N G => f e (configToPos A e)) := by
      funext A; rw [Finset.prod_apply]
    rw [hfun]
    refine Finset.aestronglyMeasurable_prod _ (fun e _ => ?_)
    have hcomp : Measurable (fun A : GaugeConfig d N G => configToPos A e) :=
      (measurable_pi_apply e).comp hsymm
    have hg : AEStronglyMeasurable (f e)
        (((Measure.pi fun _ : PosEdge d N => μ).map gaugeConfigEquiv).map
          (fun A => configToPos A e)) := by
      rw [show ((Measure.pi fun _ : PosEdge d N => μ).map gaugeConfigEquiv)
            = gaugeMeasureFrom (d := d) (N := N) μ from rfl, gaugeMeasureFrom_map_eval]
      exact hf e
    exact hg.comp_aemeasurable hcomp.aemeasurable

/-- **A multi-edge scalar product observable vanishes if any one factor has zero group
mean.**  For a *scalar* product of independent per-edge observables `∏ₑ fₑ(A e)`, if some
edge `e₀` carries an observable with vanishing Haar mean `∫ f e₀ dμ = 0`, then the full
product expectation under the lattice gauge measure is zero.  Combined with the
Schur/Fourier zero-mean facts (e.g. `∫ tr = 0`, `∫ fourier k = 0`) this kills any scalar
edge-product observable with a non-trivial factor.

NOTE on scope (do not over-read): this applies to genuine *scalar products over distinct
edges*, e.g. `∏ₑ χ(A e)`.  It does **not** apply to a Wilson *loop* `tr(∏ matrices)` —
a trace of a matrix product couples the edges and is not of the form `∏ₑ fₑ(A e)`; that
case needs the centre-eigenvalue argument and a closed loop does not vanish in general
(see `HORIZON.md` §3.3, LG6). -/
theorem integral_prod_edges_eq_zero {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure G) [IsProbabilityMeasure μ] (f : PosEdge d N → G → 𝕜)
    (hf : ∀ e, AEStronglyMeasurable (f e) μ)
    (e₀ : PosEdge d N) (hmean : ∫ g, f e₀ g ∂μ = 0) :
    ∫ A, ∏ e : PosEdge d N, f e (configToPos A e)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) = 0 := by
  rw [integral_prod_edges μ f hf]
  exact Finset.prod_eq_zero (Finset.mem_univ e₀) hmean

end YangMills
