/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure
import YangMills.ClayCore.WilsonLine

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

/-! ### The Wilson-loop centre selection rule (T3 headline) -/

open GaugeConfig in
/-- Membership-local form of the Wilson-line centre scaling: it suffices
that the rescaling holds on the traversed edges. -/
lemma wilsonLine_center_smul_of_mem {z : G} (hz : ∀ y : G, Commute z y)
    (A Az : GaugeConfig d N G)
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)))
    (hAz : ∀ e ∈ es, Az e = z * A e) :
    wilsonLine Az es = z ^ es.length * wilsonLine A es := by
  unfold wilsonLine
  have hmap : (es.map (fun e => Az e))
      = (es.map (fun e => A e)).map (fun g => z * g) := by
    rw [List.map_map]
    exact List.map_congr_left (fun e he => by
      rw [Function.comp_apply, hAz e he])
  rw [hmap, center_listProd_scaling hz, List.length_map]

open GaugeConfig in
/-- **The Wilson-loop centre selection rule (LG6/T3, headline).**
Let `μ` be a left-invariant probability measure on the matrix units, `z` a
central unit with scalar value `ω·1`, and `es` a loop traversing
positively-oriented edges.  If `ω^L ≠ 1` (for `Z_N ⊂ SU(N)`: `N ∤ L`), the
Wilson-loop expectation **vanishes**:
`∫ wilsonLoop A es ∂(gaugeMeasureFrom μ) = 0`.

Proof: the centre action fixes the measure (`integral_centerAct`) but
multiplies the loop by `ω^L` (`wilsonLine_center_smul_of_mem` +
`trace_scalarPow_mul`, fed by `centerAct_apply_pos` on positive edges), so
`(1 − ω^L)·E[W] = 0`. -/
theorem integral_wilsonLoop_eq_zero {n : ℕ}
    [MeasurableSpace (Matrix (Fin n) (Fin n) ℂ)ˣ]
    (μ : Measure (Matrix (Fin n) (Fin n) ℂ)ˣ) [IsProbabilityMeasure μ]
    [MeasurableMul (Matrix (Fin n) (Fin n) ℂ)ˣ] [μ.IsMulLeftInvariant]
    (ω : ℂ) {z : (Matrix (Fin n) (Fin n) ℂ)ˣ}
    (hzval : (z : Matrix (Fin n) (Fin n) ℂ)
      = ω • (1 : Matrix (Fin n) (Fin n) ℂ))
    (hz : ∀ y, Commute z y)
    (es : List (ConcreteEdge d N)) (hpos : ∀ e ∈ es, e.sign = true)
    (hω : ω ^ es.length ≠ 1) :
    ∫ A, wilsonLoop A es
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) = 0 := by
  -- pointwise eigenvalue under the centre action
  have hpt : ∀ A : GaugeConfig d N (Matrix (Fin n) (Fin n) ℂ)ˣ,
      wilsonLoop (centerAct z A) es = ω ^ es.length * wilsonLoop A es := by
    intro A
    unfold wilsonLoop
    rw [wilsonLine_center_smul_of_mem hz A (centerAct z A) es
      (fun e he => centerAct_apply_pos z A e (hpos e he)),
      Units.val_mul, Units.val_pow_eq_pow_val, hzval, trace_scalarPow_mul]
  -- the measure is centre-invariant
  have hinv : ∫ A, wilsonLoop A es
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ∫ A, wilsonLoop (centerAct z A) es
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
    (integral_centerAct μ z _).symm
  -- extract the eigenvalue
  have hmul : ∫ A, wilsonLoop (centerAct z A) es
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ω ^ es.length * ∫ A, wilsonLoop A es
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
    rw [show (fun A => wilsonLoop (centerAct z A) es)
        = fun A => ω ^ es.length * wilsonLoop A es from funext hpt]
    exact MeasureTheory.integral_const_mul _ _
  rw [hmul] at hinv
  have hfactor : (1 - ω ^ es.length) *
      ∫ A, wilsonLoop A es ∂(gaugeMeasureFrom (d := d) (N := N) μ) = 0 := by
    linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm hω
  · exact h2

end YangMills
