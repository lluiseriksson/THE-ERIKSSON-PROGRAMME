/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure

/-!
# LG6 (measure step) — centre invariance of the product gauge measure

The centre action on gauge configurations, defined through the positive-edge
coordinates (`docs/T3-LG6-PLAN.md`): multiply every positive edge by a fixed
group element `z`; negative edges pick up `z⁻¹` automatically through the
reversal constraint, so no `map_reverse` proof is ever needed — the action is
conjugation of coordinatewise left translation by `gaugeConfigEquiv`.

Main result: **`integral_centerAct`** — for `μ` left-invariant, the gauge
measure `gaugeMeasureFrom μ` is invariant under the centre action:
`∫ f (centerAct z A) = ∫ f A`.  Proof: transport both integrals to the
positive-edge product space along the measurable equivalence
(`integral_map_equiv`), where the action is coordinatewise left translation,
measure-preserving by `measurePreserving_pi` + `measurePreserving_mul_left`.

Combined with the proved algebraic eigenvalue `wilsonLoop_scalarCenter_smul`
(`WilsonLine.lean`), this is the measure-theoretic half of the Wilson-loop
centre selection rule (the remaining assembly is `T3-LG6-PLAN.md`).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-- `gaugeConfigEquiv` as a **measurable equivalence** (the σ-algebra on
`GaugeConfig` is by construction the comap along its inverse). -/
noncomputable def gaugeConfigMEquiv :
    (PosEdge d N → G) ≃ᵐ GaugeConfig d N G where
  toEquiv := gaugeConfigEquiv
  measurable_toFun := measurable_gaugeConfigEquiv
  measurable_invFun := by
    rw [measurable_iff_comap_le]
    exact le_rfl

/-- The **centre action** on gauge configurations: multiply every positive
edge by `z` (negative edges acquire `z⁻¹` through the reversal constraint,
handled by the equivalence). -/
noncomputable def centerAct (z : G) (A : GaugeConfig d N G) :
    GaugeConfig d N G :=
  gaugeConfigEquiv (fun e => z * configToPos A e)

/-- On positively-oriented edges, the centre action is exactly left
multiplication by `z`: `(centerAct z A) e = z * A e`. -/
lemma centerAct_apply_pos (z : G) (A : GaugeConfig d N G)
    (e : ConcreteEdge d N) (he : e.sign = true) :
    centerAct z A e = z * A e := by
  show posToFun (fun e => z * configToPos A e) e = z * A e
  unfold posToFun
  rw [dif_pos he]
  rfl

/-- **LG6: the gauge measure is invariant under the centre action.**
For a left-invariant `μ` on `G`, integrating any observable against
`gaugeMeasureFrom μ` is unchanged by the centre rescaling `centerAct z`. -/
theorem integral_centerAct (μ : Measure G) [IsProbabilityMeasure μ]
    [MeasurableMul G] [μ.IsMulLeftInvariant] (z : G)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : GaugeConfig d N G → E) :
    ∫ A, f (centerAct z A) ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ∫ A, f A ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  -- the gauge measure is the pushforward along the measurable equivalence
  have hmeas : gaugeMeasureFrom (d := d) (N := N) μ
      = Measure.map (gaugeConfigMEquiv (d := d) (N := N) (G := G))
          (Measure.pi (fun _ : PosEdge d N => μ)) := rfl
  rw [hmeas, MeasureTheory.integral_map_equiv, MeasureTheory.integral_map_equiv]
  -- on coordinates, the action is coordinatewise left translation
  have hact : ∀ x : PosEdge d N → G,
      centerAct z (gaugeConfigMEquiv x)
        = gaugeConfigMEquiv (fun e => z * x e) := by
    intro x
    unfold centerAct
    show gaugeConfigEquiv _ = gaugeConfigEquiv _
    congr 1
    funext e
    rw [show configToPos (gaugeConfigMEquiv x) = x from
      (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv x]
  simp_rw [hact]
  -- coordinatewise left translation preserves the product measure
  have hmp : MeasurePreserving
      (fun (x : PosEdge d N → G) (e : PosEdge d N) => z * x e)
      (Measure.pi (fun _ : PosEdge d N => μ))
      (Measure.pi (fun _ : PosEdge d N => μ)) :=
    measurePreserving_pi (fun _ : PosEdge d N => μ) (fun _ : PosEdge d N => μ)
      (fun _ => measurePreserving_mul_left μ z)
  exact hmp.integral_comp
    (MeasurableEquiv.piCongrRight
      (fun _ : PosEdge d N => MeasurableEquiv.mulLeft z)).measurableEmbedding
    (fun y => f (gaugeConfigMEquiv y))

end YangMills
