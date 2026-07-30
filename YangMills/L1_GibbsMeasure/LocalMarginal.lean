/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.EdgeFactorization
import YangMills.L1_GibbsMeasure.SupportFactorization

/-!
# Finite-support marginals across different product spaces

There is no canonical map from a complete gauge configuration on one torus
to a complete gauge configuration on another torus.  A thermodynamic-limit
argument does not need one.  A local marked term reads only finitely many
positive-edge coordinates, and the product Haar integral of such a term is
exactly its marginal integral over those coordinates.

`integral_pi_eq_supportMarginal` proves that reduction for one finite product
space.  `integral_pi_eq_of_supportEquiv` compares two different finite product
spaces through an equivalence of their finite supports.  Both statements are
pure product-measure calculus: no infinite-volume value and no boundary
hypothesis occurs.
-/

namespace YangMills

open MeasureTheory

open Classical in
/-- Extend an assignment on a finite coordinate set by a fixed value outside
that set. -/
noncomputable def extendOnFinset
    {ι β : Type*} (p : ι → Prop) [DecidablePred p]
    (b₀ : β) (a : {i // p i} → β) : ι → β :=
  fun i => if h : p i then a ⟨i, h⟩ else b₀

open Classical in
/-- A function depending on finitely many coordinates has the same product
integral as its restriction to that finite marginal. -/
theorem integral_pi_eq_supportMarginal
    {ι β : Type*} [Fintype ι] [MeasurableSpace β] [Nonempty β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (p : ι → Prop) [DecidablePred p] (F : (ι → β) → ℂ)
    (hF : ∀ x y : ι → β, (∀ i, p i → x i = y i) → F x = F y)
    (b₀ : β) :
    ∫ x, F x ∂(Measure.pi fun _ : ι => μ)
      = ∫ a, F (extendOnFinset p b₀ a)
          ∂(Measure.pi fun _ : {i // p i} => μ) := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => β) p
  have hmp :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p
  have hcoord : ∀ (a : {i // p i} → β) (b : {i // ¬ p i} → β) (i : ι),
      e.symm (a, b) i = if h : p i then a ⟨i, h⟩ else b ⟨i, h⟩ := by
    intro a b i
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
  let F₁ : ({i // p i} → β) → ℂ :=
    fun a => F (extendOnFinset p b₀ a)
  have hsplit : ∀ (a : {i // p i} → β) (b : {i // ¬ p i} → β),
      F (e.symm (a, b)) = F₁ a := by
    intro a b
    refine hF _ _ fun i hi => ?_
    rw [hcoord, dif_pos hi]
    simp [extendOnFinset, hi]
  have htrans :
      (∫ x, F x ∂(Measure.pi fun _ : ι => μ))
        = ∫ z, F (e.symm z)
            ∂((Measure.pi fun _ : {i // p i} => μ).prod
              (Measure.pi fun _ : {i // ¬ p i} => μ)) := by
    have hmp' := hmp.symm e
    rw [← hmp'.map_eq, MeasureTheory.integral_map_equiv]
  calc
    (∫ x, F x ∂(Measure.pi fun _ : ι => μ))
        = ∫ z, F (e.symm z)
            ∂((Measure.pi fun _ : {i // p i} => μ).prod
              (Measure.pi fun _ : {i // ¬ p i} => μ)) := htrans
    _ = ∫ z, F₁ z.1 * (1 : ℂ)
          ∂((Measure.pi fun _ : {i // p i} => μ).prod
            (Measure.pi fun _ : {i // ¬ p i} => μ)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          change F (e.symm (z.1, z.2)) = F₁ z.1 * 1
          rw [hsplit]
          ring
    _ = (∫ a, F₁ a ∂(Measure.pi fun _ : {i // p i} => μ)) *
          ∫ _b, (1 : ℂ)
            ∂(Measure.pi fun _ : {i // ¬ p i} => μ) :=
          MeasureTheory.integral_prod_mul
            (μ := Measure.pi fun _ : {i // p i} => μ)
            (ν := Measure.pi fun _ : {i // ¬ p i} => μ)
            F₁ (fun _ => (1 : ℂ))
    _ = ∫ a, F (extendOnFinset p b₀ a)
          ∂(Measure.pi fun _ : {i // p i} => μ) := by
          simp [F₁]

open Classical in
/-- **Cross-product finite-marginal bridge.**  Local functions on two
different finite coordinate types have equal product integrals when their
finite supports are equivalent and their support-restricted values agree
under that equivalence. -/
theorem integral_pi_eq_of_supportEquiv
    {ι κ β : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace β] [Nonempty β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (p : ι → Prop) (q : κ → Prop) [DecidablePred p] [DecidablePred q]
    (F : (ι → β) → ℂ) (H : (κ → β) → ℂ)
    (hF : ∀ x y : ι → β, (∀ i, p i → x i = y i) → F x = F y)
    (hH : ∀ x y : κ → β, (∀ i, q i → x i = y i) → H x = H y)
    (e : {i // p i} ≃ {i // q i}) (b₀ : β)
    (hcompat : ∀ a : {i // p i} → β,
      F (extendOnFinset p b₀ a) =
        H (extendOnFinset q b₀ (fun t => a (e.symm t)))) :
    ∫ x, F x ∂(Measure.pi fun _ : ι => μ)
      = ∫ y, H y ∂(Measure.pi fun _ : κ => μ) := by
  classical
  let E := MeasurableEquiv.piCongrLeft (fun _ : {i // q i} => β) e
  have hE : ∀ a : {i // p i} → β, E a = fun t => a (e.symm t) := by
    intro a
    funext t
    obtain ⟨s, rfl⟩ := e.surjective t
    simpa using MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : {i // q i} => β) e a s
  have hmp : MeasurePreserving E
      (Measure.pi fun _ : {i // p i} => μ)
      (Measure.pi fun _ : {i // q i} => μ) :=
    measurePreserving_piCongrLeft (fun _ : {i // q i} => μ) e
  rw [integral_pi_eq_supportMarginal μ p F hF b₀,
    integral_pi_eq_supportMarginal μ q H hH b₀]
  calc
    (∫ a, F (extendOnFinset p b₀ a)
        ∂(Measure.pi fun _ : {i // p i} => μ))
        = ∫ a, H (extendOnFinset q b₀ (E a))
            ∂(Measure.pi fun _ : {i // p i} => μ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
          change F (extendOnFinset p b₀ a) =
            H (extendOnFinset q b₀ (E a))
          rw [hE a]
          exact hcompat a
    _ = ∫ b, H (extendOnFinset q b₀ b)
          ∂(Measure.pi fun _ : {i // q i} => μ) :=
        hmp.integral_comp E.measurableEmbedding
          (fun b => H (extendOnFinset q b₀ b))

open Classical in
/-- **Gauge-configuration form of the cross-volume marginal bridge.**

The full positive-edge coordinate types of two tori need not be related.
Only the two finite supports are equivalent, and the two local functions
agree after corresponding assignments on those supports are extended by a
fixed group value.  Product Haar integration then gives equal gauge
integrals. -/
theorem integral_gaugeMeasureFrom_eq_of_supportEquiv
    {d N M : ℕ} [NeZero d] [NeZero N] [NeZero M]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (SF : Finset (PosEdge d N)) (TF : Finset (PosEdge d M))
    (F : GaugeConfig d N G → ℂ) (H : GaugeConfig d M G → ℂ)
    (hF : DependsOnPos F SF) (hH : DependsOnPos H TF)
    (e : {i // i ∈ SF} ≃ {j // j ∈ TF}) (g₀ : G)
    (hcompat : ∀ a : {i // i ∈ SF} → G,
      F (posToConfig (extendOnFinset (fun i => i ∈ SF) g₀ a)) =
        H (posToConfig (extendOnFinset (fun j => j ∈ TF) g₀
          (fun t => a (e.symm t))))) :
    ∫ A, F A ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ∫ A, H A ∂(gaugeMeasureFrom (d := d) (N := M) μ) := by
  classical
  have htransN :
      (∫ A, F A ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = ∫ x, F (gaugeConfigMEquiv x)
            ∂(Measure.pi fun _ : PosEdge d N => μ) := by
    have hmeasure :
        gaugeMeasureFrom (d := d) (N := N) μ =
          Measure.map (gaugeConfigMEquiv (d := d) (N := N) (G := G))
            (Measure.pi fun _ : PosEdge d N => μ) := rfl
    rw [hmeasure, MeasureTheory.integral_map_equiv]
  have htransM :
      (∫ A, H A ∂(gaugeMeasureFrom (d := d) (N := M) μ))
        = ∫ x, H (gaugeConfigMEquiv x)
            ∂(Measure.pi fun _ : PosEdge d M => μ) := by
    have hmeasure :
        gaugeMeasureFrom (d := d) (N := M) μ =
          Measure.map (gaugeConfigMEquiv (d := d) (N := M) (G := G))
            (Measure.pi fun _ : PosEdge d M => μ) := rfl
    rw [hmeasure, MeasureTheory.integral_map_equiv]
  rw [htransN, htransM]
  exact integral_pi_eq_of_supportEquiv μ
    (fun i => i ∈ SF) (fun j => j ∈ TF)
    (fun x => F (gaugeConfigMEquiv x))
    (fun y => H (gaugeConfigMEquiv y))
    (fun x y hxy => hF x y fun i hi => hxy i hi)
    (fun x y hxy => hH x y fun j hj => hxy j hj)
    e g₀ hcompat

end YangMills
