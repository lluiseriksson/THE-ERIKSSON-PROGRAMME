/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.PolymerExpansion
import YangMills.L1_GibbsMeasure.PolymerFactorization
import YangMills.L1_GibbsMeasure.LatticePolymerSystem
import YangMills.L1_GibbsMeasure.ClusterGeometry

/-!
# The polymer representation: `Z = Ξ` (step 2, the gate)

The lattice partition function **is** the polymer-gas partition
function of the connected lattice gas:

* `componentFamily` — the touching components of a plaquette set,
  packaged (instance-free, via `Finset.map`) as a family of polymers;
* `partitionFunction_eq_partition` — `Z = Ξ(univ)`, by the bijection
  `S ↔ (admissible family of its touching components)`:

  - forward: `componentFamily`, admissible by
    `plaqComponents_support_disjoint`;
  - backward: union; mutually inverse by `plaqComponents_biUnion` and
    the reconstruction `plaqComponents_biUnion_eq`;
  - values: the Mayer product over `S` factors over components
    (`integral_prod_prod_plaquetteWeight_of_pairwiseDisjoint`), and the
    per-component integral *is* the polymer activity by definition.

Composed with `partition_eq_exp_clusterSum_of_kp` (Mayer–Ursell) this
gives `Z = exp(clusterSum)` for the connected lattice gas — the
representation that the correlation chain (B2) differentiates.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open KP MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- The touching components of a plaquette set, as a family of polymers
of the connected lattice gas (an instance-free `Finset.map` along the
injective lift). -/
noncomputable def componentFamily (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (S : Finset (ConcretePlaquette d N)) :
    Finset (connectedLatticePolymerSystem (d := d) (N := N) μ pe β).Polymer :=
  (plaqComponents S).attach.map
    ⟨fun c => ⟨c.1, plaqComponents_polymer_mem c.2⟩, fun a b h =>
      Subtype.ext (Subtype.mk_eq_mk.mp (show
        (⟨a.1, plaqComponents_polymer_mem a.2⟩ :
          { c : Finset (ConcretePlaquette d N) //
            c.Nonempty ∧ IsConnectedPolymer c })
          = ⟨b.1, plaqComponents_polymer_mem b.2⟩ from h))⟩

lemma mem_componentFamily_iff {μ : Measure G} {pe : G → ℝ} {β : ℝ}
    {S : Finset (ConcretePlaquette d N)}
    {X : (connectedLatticePolymerSystem (d := d) (N := N) μ pe β).Polymer} :
    X ∈ componentFamily (d := d) (N := N) μ pe β S
      ↔ X.1 ∈ plaqComponents S := by
  unfold componentFamily
  rw [Finset.mem_map]
  constructor
  · rintro ⟨c, -, rfl⟩
    exact c.2
  · intro h
    exact ⟨⟨X.1, h⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

/-- The activity product over the component family is the product of
the per-component Mayer integrals. -/
lemma prod_componentFamily (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (S : Finset (ConcretePlaquette d N)) :
    ∏ X ∈ componentFamily (d := d) (N := N) μ pe β S,
      (connectedLatticePolymerSystem (d := d) (N := N) μ pe β).activity X
    = ∏ c ∈ plaqComponents S,
        ((∫ A0, ∏ p ∈ c, plaquetteWeight pe β A0 p
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
  unfold componentFamily
  rw [Finset.prod_map]
  refine Eq.trans (Finset.prod_congr rfl (fun c _ => ?_))
    (Finset.prod_attach (plaqComponents S) (fun c =>
      ((∫ A0, ∏ p ∈ c, plaquetteWeight pe β A0 p
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)))
  rfl

set_option maxHeartbeats 3200000 in
open Classical in
/-- **STEP 2, THE GATE: `Z = Ξ`.**  The lattice partition function
equals the polymer partition function of the connected lattice gas. -/
theorem partitionFunction_eq_partition
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ}
    (hpe_meas : Measurable pe) {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    ((partitionFunction (d := d) (N := N) μ pe β : ℝ) : ℂ)
      = KP.partition
          (connectedLatticePolymerSystem (d := d) (N := N) μ pe β)
          Finset.univ := by
  classical
  calc ((partitionFunction (d := d) (N := N) μ pe β : ℝ) : ℂ)
      = ∑ S ∈ (Finset.univ : Finset (ConcretePlaquette d N)).powerset,
          ((∫ A0, ∏ p ∈ S, plaquetteWeight pe β A0 p
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
        rw [partitionFunction_eq_sum_plaquetteSets' μ hpe_meas hpe β]
        push_cast
        rfl
    _ = KP.partition
          (connectedLatticePolymerSystem (d := d) (N := N) μ pe β)
          Finset.univ := by
        unfold KP.partition
        refine Finset.sum_nbij'
          (componentFamily (d := d) (N := N) μ pe β)
          (fun F => F.biUnion (fun X => X.1)) ?_ ?_ ?_ ?_ ?_
        · -- forward membership: component families are admissible
          intro S _
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
          intro X hX Y hY hXY
          have hXc := mem_componentFamily_iff.mp hX
          have hYc := mem_componentFamily_iff.mp hY
          have hne' : (X.1 : Finset (ConcretePlaquette d N)) ≠ Y.1 :=
            fun h => hXY (Subtype.ext h)
          intro hinc
          exact hinc (plaqComponents_support_disjoint hXc hYc hne')
        · -- backward membership
          intro F _
          exact Finset.mem_powerset.mpr (Finset.subset_univ _)
        · -- left inverse: the union of the components is the set
          intro S _
          show (componentFamily (d := d) (N := N) μ pe β S).biUnion
            (fun X => X.1) = S
          ext p
          rw [Finset.mem_biUnion]
          constructor
          · rintro ⟨X, hX, hp⟩
            exact plaqComponents_subset
              (mem_componentFamily_iff.mp hX) hp
          · intro hp
            rw [← plaqComponents_biUnion S, Finset.mem_biUnion] at hp
            obtain ⟨c, hc, hpc⟩ := hp
            exact ⟨⟨c, plaqComponents_polymer_mem hc⟩,
              mem_componentFamily_iff.mpr hc, hpc⟩
        · -- right inverse: the components of the union are the family
          intro F hF
          rw [Finset.mem_filter] at hF
          obtain ⟨-, hadm⟩ := hF
          show componentFamily (d := d) (N := N) μ pe β
            (F.biUnion (fun X => X.1)) = F
          have hrec : plaqComponents (F.biUnion (fun X => X.1))
              = F.image (fun X => X.1) := by
            have hbu : (F.image (fun X => X.1)).biUnion id
                = F.biUnion (fun X => X.1) := by
              ext p
              simp only [Finset.mem_biUnion, Finset.mem_image, id_eq]
              constructor
              · rintro ⟨c, ⟨X, hX, rfl⟩, hp⟩
                exact ⟨X, hX, hp⟩
              · rintro ⟨X, hX, hp⟩
                exact ⟨X.1, ⟨X, hX, rfl⟩, hp⟩
            rw [← hbu]
            refine plaqComponents_biUnion_eq ?_ ?_ ?_
            · intro c hc
              rw [Finset.mem_image] at hc
              obtain ⟨X, -, rfl⟩ := hc
              exact X.2.1
            · intro c hc
              rw [Finset.mem_image] at hc
              obtain ⟨X, -, rfl⟩ := hc
              exact X.2.2
            · intro c hc c' hc' hne
              rw [Finset.mem_image] at hc hc'
              obtain ⟨X, hX, rfl⟩ := hc
              obtain ⟨Y, hY, rfl⟩ := hc'
              have hXY : X ≠ Y := fun h => hne (by rw [h])
              exact not_not.mp (hadm X hX Y hY hXY)
          ext X
          rw [mem_componentFamily_iff, hrec, Finset.mem_image]
          constructor
          · rintro ⟨Y, hY, hYX⟩
            rwa [Subtype.ext hYX] at hY
          · intro hX
            exact ⟨X, hX, rfl⟩
        · -- values: the Mayer product factors over components, and the
          -- per-component integral is the activity by definition
          intro S _
          have hpd : ∀ c ∈ plaqComponents S, ∀ c' ∈ plaqComponents S,
              c ≠ c' → Disjoint c c' :=
            fun c hc c' hc' hne => plaqComponents_disjoint hc hc' hne
          have hsupp : ∀ c ∈ plaqComponents S, ∀ c' ∈ plaqComponents S,
              c ≠ c' → Disjoint (c.biUnion plaquetteSupport)
                (c'.biUnion plaquetteSupport) :=
            fun c hc c' hc' hne =>
              plaqComponents_support_disjoint hc hc' hne
          have hpdset : Set.PairwiseDisjoint
              (↑(plaqComponents S) : Set (Finset (ConcretePlaquette d N)))
              (id : Finset (ConcretePlaquette d N) →
                Finset (ConcretePlaquette d N)) :=
            fun c hc c' hc' hne => plaqComponents_disjoint hc hc' hne
          have hfg : (fun A0 : GaugeConfig d N G =>
              ∏ p ∈ S, plaquetteWeight pe β A0 p)
              = fun A0 => ∏ c ∈ plaqComponents S,
                  ∏ p ∈ c, plaquetteWeight pe β A0 p := by
            funext A0
            conv_lhs => rw [← plaqComponents_biUnion S]
            rw [Finset.prod_biUnion hpdset]
            simp only [id_eq]
          calc ((∫ A0, ∏ p ∈ S, plaquetteWeight pe β A0 p
                  ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)
              = ((∫ A0, ∏ c ∈ plaqComponents S,
                    ∏ p ∈ c, plaquetteWeight pe β A0 p
                  ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
                rw [hfg]
            _ = ((∏ c ∈ plaqComponents S,
                    ∫ A0, ∏ p ∈ c, plaquetteWeight pe β A0 p
                  ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
                rw [integral_prod_prod_plaquetteWeight_of_pairwiseDisjoint
                  μ pe β (plaqComponents S) hsupp hpd]
            _ = ∏ c ∈ plaqComponents S,
                  ((∫ A0, ∏ p ∈ c, plaquetteWeight pe β A0 p
                    ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) :=
                Complex.ofReal_prod _ _
            _ = ∏ X ∈ componentFamily (d := d) (N := N) μ pe β S,
                  (connectedLatticePolymerSystem
                    (d := d) (N := N) μ pe β).activity X :=
                (prod_componentFamily μ pe β S).symm

end YangMills
