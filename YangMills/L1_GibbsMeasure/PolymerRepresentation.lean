/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.PolymerExpansion
import YangMills.L1_GibbsMeasure.PolymerFactorization
import YangMills.L1_GibbsMeasure.LatticePolymerSystem
import YangMills.L1_GibbsMeasure.ClusterGeometry
import YangMills.L1_GibbsMeasure.WeightedGas
import YangMills.KP.MayerInversion

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

open Classical in
/-- **`Z = exp(clusterSum)` for the connected lattice gas** — the
polymer representation composed with the Mayer–Ursell inversion, under
the volume-uniform KP smallness (constants depend only on `d, B, β, t`).
In particular the partition function never vanishes at high
temperature. -/
theorem partitionFunction_eq_exp_clusterSum
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ}
    (hpe_meas : Measurable pe) {B : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (β t : ℝ) (ht0 : 0 ≤ t)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp t) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp t) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp t))) ≤ t) :
    ((partitionFunction (d := d) (N := N) μ pe β : ℝ) : ℂ)
      = Complex.exp (KP.clusterSum
          (connectedLatticePolymerSystem (d := d) (N := N) μ pe β)) := by
  rw [partitionFunction_eq_partition μ hpe_meas hpe β]
  exact KP.partition_eq_exp_clusterSum_of_kp _
    (connectedLatticePolymerSystem_kpCriterion_volumeUniform
      μ hpe β t ht0 hr hsmall)

/-! ### The weighted polymer representation (B2, brick W2):
`Z[w] = Ξ[w]` for arbitrary local weight families -/

/-- The **weighted connected lattice gas**: same polymers as the
connected gas, activities given by an arbitrary weight family. -/
noncomputable def weightedLatticePolymerSystem (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ) :
    KP.PolymerSystem where
  Polymer := { c : Finset (ConcretePlaquette d N) //
    c.Nonempty ∧ IsConnectedPolymer c }
  incomp c c' := ¬ Disjoint (c.1.biUnion plaquetteSupport)
    (c'.1.biUnion plaquetteSupport)
  incomp_symm := by
    intro a b h hd
    exact h hd.symm
  incomp_self := by
    intro c hdisj
    obtain ⟨p, hp⟩ := c.2.1
    have hmem : (p.edges 0).pos ∈ c.1.biUnion plaquetteSupport :=
      Finset.mem_biUnion.mpr ⟨p, hp, by simp [plaquetteSupport]⟩
    exact (Finset.disjoint_left.mp hdisj hmem) hmem
  activity c := ((∫ A, ∏ p ∈ c.1, w A p
    ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)

noncomputable instance (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ) :
    Fintype (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer := by
  classical
  exact inferInstanceAs (Fintype { c : Finset (ConcretePlaquette d N) //
    c.Nonempty ∧ IsConnectedPolymer c })

/-- The component family, lifted into the weighted gas. -/
noncomputable def weightedComponentFamily (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (S : Finset (ConcretePlaquette d N)) :
    Finset (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer :=
  (plaqComponents S).attach.map
    ⟨fun c => ⟨c.1, plaqComponents_polymer_mem c.2⟩, fun a b h =>
      Subtype.ext (Subtype.mk_eq_mk.mp (show
        (⟨a.1, plaqComponents_polymer_mem a.2⟩ :
          { c : Finset (ConcretePlaquette d N) //
            c.Nonempty ∧ IsConnectedPolymer c })
          = ⟨b.1, plaqComponents_polymer_mem b.2⟩ from h))⟩

lemma mem_weightedComponentFamily_iff {μ : Measure G}
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {S : Finset (ConcretePlaquette d N)}
    {X : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer} :
    X ∈ weightedComponentFamily (d := d) (N := N) μ w S
      ↔ X.1 ∈ plaqComponents S := by
  unfold weightedComponentFamily
  rw [Finset.mem_map]
  constructor
  · rintro ⟨c, -, rfl⟩
    exact c.2
  · intro h
    exact ⟨⟨X.1, h⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

/-- The activity product over the weighted component family. -/
lemma prod_weightedComponentFamily (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (S : Finset (ConcretePlaquette d N)) :
    ∏ X ∈ weightedComponentFamily (d := d) (N := N) μ w S,
      (weightedLatticePolymerSystem (d := d) (N := N) μ w).activity X
    = ∏ c ∈ plaqComponents S,
        ((∫ A0, ∏ p ∈ c, w A0 p
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
  unfold weightedComponentFamily
  rw [Finset.prod_map]
  refine Eq.trans (Finset.prod_congr rfl (fun c _ => ?_))
    (Finset.prod_attach (plaqComponents S) (fun c =>
      ((∫ A0, ∏ p ∈ c, w A0 p
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)))
  rfl

set_option maxHeartbeats 3200000 in
open Classical in
/-- **`Z[w] = Ξ[w]` (B2, brick W2):** the weighted partition function
equals the polymer partition function of the weighted gas, for every
bounded measurable local weight family. -/
theorem weightedPartition_eq_partition
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hloc : IsLocalWeight (d := d) (N := N) (G := G) w)
    (hmeas : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    {δ : ℝ} (hbd : ∀ A p, |w A p| ≤ δ) :
    ((weightedPartition (d := d) (N := N) μ w : ℝ) : ℂ)
      = KP.partition (weightedLatticePolymerSystem (d := d) (N := N) μ w)
          Finset.univ := by
  classical
  calc ((weightedPartition (d := d) (N := N) μ w : ℝ) : ℂ)
      = ∑ S ∈ (Finset.univ : Finset (ConcretePlaquette d N)).powerset,
          ((∫ A0, ∏ p ∈ S, w A0 p
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
        rw [weightedPartition_eq_sum μ hmeas hbd]
        push_cast
        rfl
    _ = KP.partition
          (weightedLatticePolymerSystem (d := d) (N := N) μ w)
          Finset.univ := by
        unfold KP.partition
        refine Finset.sum_nbij'
          (weightedComponentFamily (d := d) (N := N) μ w)
          (fun F => F.biUnion (fun X => X.1)) ?_ ?_ ?_ ?_ ?_
        · -- forward membership: component families are admissible
          intro S _
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
          intro X hX Y hY hXY
          have hXc := mem_weightedComponentFamily_iff.mp hX
          have hYc := mem_weightedComponentFamily_iff.mp hY
          have hne' : (X.1 : Finset (ConcretePlaquette d N)) ≠ Y.1 :=
            fun h => hXY (Subtype.ext h)
          intro hinc
          exact hinc (plaqComponents_support_disjoint hXc hYc hne')
        · -- backward membership
          intro F _
          exact Finset.mem_powerset.mpr (Finset.subset_univ _)
        · -- left inverse
          intro S _
          show (weightedComponentFamily (d := d) (N := N) μ w S).biUnion
            (fun X => X.1) = S
          ext p
          rw [Finset.mem_biUnion]
          constructor
          · rintro ⟨X, hX, hp⟩
            exact plaqComponents_subset
              (mem_weightedComponentFamily_iff.mp hX) hp
          · intro hp
            rw [← plaqComponents_biUnion S, Finset.mem_biUnion] at hp
            obtain ⟨c, hc, hpc⟩ := hp
            exact ⟨⟨c, plaqComponents_polymer_mem hc⟩,
              mem_weightedComponentFamily_iff.mpr hc, hpc⟩
        · -- right inverse
          intro F hF
          rw [Finset.mem_filter] at hF
          obtain ⟨-, hadm⟩ := hF
          show weightedComponentFamily (d := d) (N := N) μ w
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
          rw [mem_weightedComponentFamily_iff, hrec, Finset.mem_image]
          constructor
          · rintro ⟨Y, hY, hYX⟩
            rwa [Subtype.ext hYX] at hY
          · intro hX
            exact ⟨X, hX, rfl⟩
        · -- values
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
              ∏ p ∈ S, w A0 p)
              = fun A0 => ∏ c ∈ plaqComponents S,
                  ∏ p ∈ c, w A0 p := by
            funext A0
            conv_lhs => rw [← plaqComponents_biUnion S]
            rw [Finset.prod_biUnion hpdset]
            simp only [id_eq]
          calc ((∫ A0, ∏ p ∈ S, w A0 p
                  ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)
              = ((∫ A0, ∏ c ∈ plaqComponents S,
                    ∏ p ∈ c, w A0 p
                  ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
                rw [hfg]
            _ = ((∏ c ∈ plaqComponents S,
                    ∫ A0, ∏ p ∈ c, w A0 p
                  ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
                rw [integral_prod_prod_weight_of_pairwiseDisjoint
                  μ hloc (plaqComponents S) hsupp hpd]
            _ = ∏ c ∈ plaqComponents S,
                  ((∫ A0, ∏ p ∈ c, w A0 p
                    ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) :=
                Complex.ofReal_prod _ _
            _ = ∏ X ∈ weightedComponentFamily (d := d) (N := N) μ w S,
                  (weightedLatticePolymerSystem
                    (d := d) (N := N) μ w).activity X :=
                (prod_weightedComponentFamily μ w S).symm

/-! ### W3: the volume-uniform KP criterion for the weighted gas -/

/-- Activity smallness for the weighted gas: `‖z(c)‖ ≤ δ^{|c|}` under
the uniform weight bound. -/
theorem norm_weightedLatticePolymerSystem_activity_le
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {δ : ℝ} (hbd : ∀ A p, |w A p| ≤ δ)
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer) :
    ‖(weightedLatticePolymerSystem (d := d) (N := N) μ w).activity c‖
      ≤ δ ^ c.1.card := by
  classical
  show ‖((∫ A, ∏ p ∈ c.1, w A p
    ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hbound := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := gaugeMeasureFrom (d := d) (N := N) μ)
    (f := fun A : GaugeConfig d N G => ∏ p ∈ c.1, w A p)
    (C := δ ^ c.1.card) ?_
  · rw [Real.norm_eq_abs] at hbound
    simpa [measure_univ] using hbound
  · refine MeasureTheory.ae_of_all _ fun A => ?_
    rw [Real.norm_eq_abs, Finset.abs_prod]
    calc ∏ p ∈ c.1, |w A p|
        ≤ ∏ _p ∈ c.1, δ :=
          Finset.prod_le_prod (fun p _ => abs_nonneg _)
            (fun p _ => hbd A p)
      _ = δ ^ c.1.card := by rw [Finset.prod_const]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **The volume-uniform KP criterion for the weighted gas** under the
uniform smallness `|w| ≤ δ`: verbatim transport of the connected-gas
criterion with `x := δ·e^t`; the entropy engine
(`sum_connectedPolymers_through_le`) is weight-free. -/
theorem weightedLatticePolymerSystem_kpCriterion_volumeUniform
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hbd : ∀ A p, |w A p| ≤ δ)
    (t : ℝ) (ht0 : 0 ≤ t)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp t) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((δ * Real.exp t) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp t))) ≤ t) :
    KPCriterion (weightedLatticePolymerSystem (d := d) (N := N) μ w)
      (fun c => t * (c.1.card : ℝ)) := by
  classical
  set x : ℝ := δ * Real.exp t with hxdef
  have hx : (0 : ℝ) ≤ x := mul_nonneg hδ0 (Real.exp_pos t).le
  set S : ℝ := x / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x) with hSdef
  have hden : (0 : ℝ) < 1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x := by
    rw [hxdef]; linarith
  have hS0 : (0 : ℝ) ≤ S := div_nonneg hx hden.le
  -- the volume-uniform per-plaquette bound
  have hthrough : ∀ p : ConcretePlaquette d N,
      (∑ Y ∈ (Finset.univ :
        Finset (weightedLatticePolymerSystem (d := d) (N := N)
          μ w).Polymer).filter (fun Y => p ∈ Y.1),
        x ^ Y.1.card) ≤ S := by
    intro p
    have h := sum_connectedPolymers_through_le (d := d) (N := N) p x hx
      (by rw [hxdef] at *; exact hr)
    convert h using 2
  constructor
  · intro c
    positivity
  · intro c
    have hterm : ∀ Y : (weightedLatticePolymerSystem (d := d) (N := N)
        μ w).Polymer,
        ‖(weightedLatticePolymerSystem (d := d) (N := N) μ w).activity Y‖ *
          Real.exp (t * (Y.1.card : ℝ)) ≤ x ^ Y.1.card := by
      intro Y
      have h1 := norm_weightedLatticePolymerSystem_activity_le
        (d := d) (N := N) μ hbd Y
      have h2 : Real.exp (t * (Y.1.card : ℝ)) = Real.exp t ^ Y.1.card := by
        rw [mul_comm, ← Real.exp_nat_mul]
      rw [hxdef, h2, mul_pow]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    -- indicator domination: every incompatible polymer is seen through a
    -- touching plaquette
    have hdom : ∀ Y ∈ (Finset.univ :
        Finset (weightedLatticePolymerSystem (d := d) (N := N)
          μ w).Polymer).filter
        (fun Y => (weightedLatticePolymerSystem (d := d) (N := N)
          μ w).incomp c Y),
        x ^ Y.1.card ≤ ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q p),
          (if p ∈ Y.1 then x ^ Y.1.card else 0) := by
      intro Y hY
      rw [Finset.mem_filter] at hY
      have hinc : ¬ Disjoint (c.1.biUnion plaquetteSupport)
          (Y.1.biUnion plaquetteSupport) := hY.2
      obtain ⟨e, hec, heY⟩ := Finset.not_disjoint_iff.mp hinc
      obtain ⟨q₀, hq₀, heq₀⟩ := Finset.mem_biUnion.mp hec
      obtain ⟨p₀, hp₀, hep₀⟩ := Finset.mem_biUnion.mp heY
      have htouch : plaquetteTouches q₀ p₀ := fun hd =>
        (Finset.disjoint_left.mp hd heq₀) hep₀
      have hp₀mem : p₀ ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q₀ p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, htouch⟩
      have hinner : x ^ Y.1.card ≤ ∑ p ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q₀ p),
          (if p ∈ Y.1 then x ^ Y.1.card else 0) := by
        have h := Finset.single_le_sum
          (f := fun p => if p ∈ Y.1 then x ^ Y.1.card else 0)
          (fun p _ => by positivity) hp₀mem
        simp only [hp₀, if_true] at h
        exact h
      refine le_trans hinner ?_
      exact Finset.single_le_sum
        (f := fun q => ∑ p ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q p),
          (if p ∈ Y.1 then x ^ Y.1.card else 0))
        (fun q _ => Finset.sum_nonneg fun p _ => by positivity) hq₀
    calc ∑ Y ∈ (Finset.univ :
          Finset (weightedLatticePolymerSystem (d := d) (N := N)
            μ w).Polymer).filter
          (fun Y => (weightedLatticePolymerSystem (d := d) (N := N)
            μ w).incomp c Y),
          ‖(weightedLatticePolymerSystem (d := d) (N := N) μ w).activity Y‖ *
            Real.exp (t * (Y.1.card : ℝ))
        ≤ ∑ Y ∈ (Finset.univ :
            Finset (weightedLatticePolymerSystem (d := d) (N := N)
              μ w).Polymer).filter
            (fun Y => (weightedLatticePolymerSystem (d := d) (N := N)
              μ w).incomp c Y),
            x ^ Y.1.card :=
          Finset.sum_le_sum fun Y _ => hterm Y
      _ ≤ ∑ Y ∈ (Finset.univ :
            Finset (weightedLatticePolymerSystem (d := d) (N := N)
              μ w).Polymer).filter
            (fun Y => (weightedLatticePolymerSystem (d := d) (N := N)
              μ w).incomp c Y),
            ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
              Finset (ConcretePlaquette d N)).filter
                (fun p => plaquetteTouches q p),
              (if p ∈ Y.1 then x ^ Y.1.card else 0) :=
          Finset.sum_le_sum hdom
      _ ≤ ∑ Y ∈ (Finset.univ :
            Finset (weightedLatticePolymerSystem (d := d) (N := N)
              μ w).Polymer),
            ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
              Finset (ConcretePlaquette d N)).filter
                (fun p => plaquetteTouches q p),
              (if p ∈ Y.1 then x ^ Y.1.card else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun Y _ _ => Finset.sum_nonneg fun q _ =>
              Finset.sum_nonneg fun p _ => by positivity)
      _ = ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
              (fun p => plaquetteTouches q p),
            ∑ Y ∈ (Finset.univ :
              Finset (weightedLatticePolymerSystem (d := d) (N := N)
                μ w).Polymer),
              (if p ∈ Y.1 then x ^ Y.1.card else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
      _ = ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
              (fun p => plaquetteTouches q p),
            ∑ Y ∈ (Finset.univ :
              Finset (weightedLatticePolymerSystem (d := d) (N := N)
                μ w).Polymer).filter (fun Y => p ∈ Y.1),
              x ^ Y.1.card := by
          refine Finset.sum_congr rfl fun q _ => ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          exact (Finset.sum_filter _ _).symm
      _ ≤ ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
              (fun p => plaquetteTouches q p), S := by
          refine Finset.sum_le_sum fun q _ => ?_
          exact Finset.sum_le_sum fun p _ => hthrough p
      _ ≤ ∑ q ∈ c.1, ((16 * d : ℕ) : ℝ) * S := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hS0
          exact_mod_cast card_plaquettesTouching_le q
      _ = (c.1.card : ℝ) * (((16 * d : ℕ) : ℝ) * S) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (c.1.card : ℝ) * t := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hSdef, hxdef]
          exact hsmall
      _ = t * (c.1.card : ℝ) := mul_comm _ _

open Classical in
/-- **`Z[w] = exp(clusterSum[w])` (B2, brick W3):** the weighted
partition function exponentiates the weighted cluster sum, for every
bounded measurable local weight family under volume-uniform smallness
(constants depend only on `d, δ, t`). -/
theorem weightedPartition_eq_exp_clusterSum
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hloc : IsLocalWeight (d := d) (N := N) (G := G) w)
    (hmeas : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hbd : ∀ A p, |w A p| ≤ δ)
    (t : ℝ) (ht0 : 0 ≤ t)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp t) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((δ * Real.exp t) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp t))) ≤ t) :
    ((weightedPartition (d := d) (N := N) μ w : ℝ) : ℂ)
      = Complex.exp (KP.clusterSum
          (weightedLatticePolymerSystem (d := d) (N := N) μ w)) := by
  rw [weightedPartition_eq_partition μ hloc hmeas hbd]
  exact KP.partition_eq_exp_clusterSum_of_kp _
    (weightedLatticePolymerSystem_kpCriterion_volumeUniform
      μ hδ0 hbd t ht0 hr hsmall)

/-! ### W4c openers: activity congruence off the deformed region -/

/-- Weight families that agree off a region have equal activities on
polymers disjoint from it — the per-polymer covariance cancellation. -/
lemma weightedLatticePolymerSystem_activity_congr
    (μ : Measure G)
    {w₁ w₂ : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {T : Finset (ConcretePlaquette d N)}
    (h : ∀ (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
      p ∉ T → w₁ A p = w₂ A p)
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w₁).Polymer)
    (hc : Disjoint c.1 T) :
    (weightedLatticePolymerSystem (d := d) (N := N) μ w₁).activity c
      = (weightedLatticePolymerSystem (d := d) (N := N) μ w₂).activity c := by
  show ((∫ A, ∏ p ∈ c.1, w₁ A p
      ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)
    = ((∫ A, ∏ p ∈ c.1, w₂ A p
      ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)
  congr 1
  refine congrArg _ (funext fun A => ?_)
  refine Finset.prod_congr rfl fun p hp => ?_
  exact h A p (Finset.disjoint_left.mp hc hp)

/-- The Ursell coefficients of the weighted gases agree — the
incompatibility structure is weight-independent. -/
lemma weightedLatticePolymerSystem_ursell_eq
    (μ : Measure G)
    (w₁ w₂ : GaugeConfig d N G → ConcretePlaquette d N → ℝ) {n : ℕ}
    (X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ w₁).Polymer) :
    KP.ursell (weightedLatticePolymerSystem (d := d) (N := N) μ w₁) X
      = KP.ursell (weightedLatticePolymerSystem (d := d) (N := N) μ w₂) X :=
  rfl

open Classical in
/-- **The four-gas cancellation (W4c):** the inclusion–exclusion
combination of cluster terms — `FG + base − F − G` — vanishes on every
tuple that misses either deformation region.  The surviving tuples
meet BOTH regions: they are the connecting clusters. -/
lemma cluster_term_four_cancel
    (μ : Measure G)
    (w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (S T : Finset (ConcretePlaquette d N)) {n : ℕ}
    (X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer)
    (hX : (∀ i, Disjoint (X i).1 S) ∨ (∀ i, Disjoint (X i).1 T)) :
    (KP.ursell (weightedLatticePolymerSystem (d := d) (N := N) μ w) X : ℂ) *
        ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ
          (deformWeight w g (S ∪ T))).activity (X i)
      + (KP.ursell (weightedLatticePolymerSystem (d := d) (N := N) μ w) X : ℂ) *
        ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ w).activity (X i)
      - (KP.ursell (weightedLatticePolymerSystem (d := d) (N := N) μ w) X : ℂ) *
        ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ
          (deformWeight w g S)).activity (X i)
      - (KP.ursell (weightedLatticePolymerSystem (d := d) (N := N) μ w) X : ℂ) *
        ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ
          (deformWeight w g T)).activity (X i) = 0 := by
  rcases hX with h | h
  · -- the tuple misses S: `FG = G` and `F = base`
    have h1 : ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ
        (deformWeight w g (S ∪ T))).activity (X i)
        = ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ
          (deformWeight w g T)).activity (X i) :=
      Finset.prod_congr rfl fun i _ =>
        weightedLatticePolymerSystem_activity_congr μ
          (fun A p hp => deformWeight_union_of_not_mem_left hp)
          (X i) (h i)
    have h2 : ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ
        (deformWeight w g S)).activity (X i)
        = ∏ i, (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).activity (X i) :=
      Finset.prod_congr rfl fun i _ =>
        weightedLatticePolymerSystem_activity_congr μ
          (fun A p hp => deformWeight_of_not_mem hp)
          (X i) (h i)
    rw [h1, h2]
    ring
  · -- the tuple misses T: `FG = F` and `G = base`
    have h1 : ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ
        (deformWeight w g (S ∪ T))).activity (X i)
        = ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ
          (deformWeight w g S)).activity (X i) :=
      Finset.prod_congr rfl fun i _ =>
        weightedLatticePolymerSystem_activity_congr μ
          (fun A p hp => deformWeight_union_of_not_mem_right hp)
          (X i) (h i)
    have h2 : ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ
        (deformWeight w g T)).activity (X i)
        = ∏ i, (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).activity (X i) :=
      Finset.prod_congr rfl fun i _ =>
        weightedLatticePolymerSystem_activity_congr μ
          (fun A p hp => deformWeight_of_not_mem hp)
          (X i) (h i)
    rw [h1, h2]
    ring

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Per-layer inclusion–exclusion (W4c):** at each cluster order the
four-gas combination collapses to a sum over connecting tuples only —
tuples meeting BOTH deformation regions. -/
lemma cluster_layer_inclusion_exclusion
    (μ : Measure G)
    (w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (S T : Finset (ConcretePlaquette d N)) (n : ℕ) :
    (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g (S ∪ T))).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g (S ∪ T))) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i)
    + (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ w) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ w).activity (X i)
    - (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g S)).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g S)) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g S)).activity (X i)
    - (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g T)).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g T)) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g T)).activity (X i)
    = (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
          (weightedLatticePolymerSystem
            (d := d) (N := N) μ w).Polymer)).filter
          (fun X => (∃ i, ¬ Disjoint (X i).1 S) ∧
            (∃ i, ¬ Disjoint (X i).1 T)),
        ((KP.ursell (weightedLatticePolymerSystem
            (d := d) (N := N) μ w) X : ℂ) *
            ∏ i, (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i)
          + (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ w) X : ℂ) *
            ∏ i, (weightedLatticePolymerSystem
              (d := d) (N := N) μ w).activity (X i)
          - (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ w) X : ℂ) *
            ∏ i, (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g S)).activity (X i)
          - (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ w) X : ℂ) *
            ∏ i, (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g T)).activity (X i)) := by
  classical
  -- identify the four full sums over the common index type
  have e1 : (∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
        (d := d) (N := N) μ (deformWeight w g (S ∪ T))).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g (S ∪ T))) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i))
      = ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ w) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i) :=
    rfl
  have e3 : (∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
        (d := d) (N := N) μ (deformWeight w g S)).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g S)) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g S)).activity (X i))
      = ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ w) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g S)).activity (X i) :=
    rfl
  have e4 : (∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
        (d := d) (N := N) μ (deformWeight w g T)).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g T)) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g T)).activity (X i))
      = ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ w) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g T)).activity (X i) :=
    rfl
  rw [e1, e3, e4, ← mul_add, ← mul_sub, ← mul_sub]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine (Finset.sum_filter_of_ne ?_).symm
  intro X _ hne
  by_contra hnc
  refine hne ?_
  have hX : (∀ i, Disjoint (X i).1 S) ∨ (∀ i, Disjoint (X i).1 T) := by
    rw [not_and_or] at hnc
    rcases hnc with h | h
    · left
      intro i
      by_contra hd
      exact h ⟨i, hd⟩
    · right
      intro i
      by_contra hd
      exact h ⟨i, hd⟩
  exact cluster_term_four_cancel μ w g S T X hX

open Classical in
/-- **The cluster-sum inclusion–exclusion (W4c, the endpoint):**
`K_{FG} + K − K_F − K_G` is the cluster sum over CONNECTING tuples —
tuples meeting both deformation regions.  Combined with
`weightedPartition_eq_exp_clusterSum` for the four gases this is the
covariance exponent of the correlation chain. -/
theorem clusterSum_inclusion_exclusion
    (μ : Measure G)
    (w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (S T : Finset (ConcretePlaquette d N))
    (h1 : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g (S ∪ T))).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g (S ∪ T))) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i)))
    (h2 : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ w) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ w).activity (X i)))
    (h3 : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g S)).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g S)) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g S)).activity (X i)))
    (h4 : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g T)).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g T)) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g T)).activity (X i))) :
    KP.clusterSum (weightedLatticePolymerSystem
        (d := d) (N := N) μ (deformWeight w g (S ∪ T)))
      + KP.clusterSum (weightedLatticePolymerSystem (d := d) (N := N) μ w)
      - KP.clusterSum (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g S))
      - KP.clusterSum (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g T))
    = ∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
            (weightedLatticePolymerSystem
              (d := d) (N := N) μ w).Polymer)).filter
            (fun X => (∃ i, ¬ Disjoint (X i).1 S) ∧
              (∃ i, ¬ Disjoint (X i).1 T)),
          ((KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i)
            + (KP.ursell (weightedLatticePolymerSystem
                (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ w).activity (X i)
            - (KP.ursell (weightedLatticePolymerSystem
                (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g S)).activity (X i)
            - (KP.ursell (weightedLatticePolymerSystem
                (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g T)).activity (X i)) := by
  classical
  calc KP.clusterSum (weightedLatticePolymerSystem
        (d := d) (N := N) μ (deformWeight w g (S ∪ T)))
      + KP.clusterSum (weightedLatticePolymerSystem (d := d) (N := N) μ w)
      - KP.clusterSum (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g S))
      - KP.clusterSum (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g T))
      = (∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g (S ∪ T))).Polymer,
            (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g (S ∪ T))) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i))
        + (∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
              (d := d) (N := N) μ w).Polymer,
            (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ w).activity (X i))
        - (∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g S)).Polymer,
            (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g S)) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g S)).activity (X i))
        - (∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g T)).Polymer,
            (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g T)) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g T)).activity (X i)) :=
      rfl
    _ = ∑' n : ℕ, ((((n + 1).factorial : ℂ))⁻¹ *
          ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g (S ∪ T))).Polymer,
            (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g (S ∪ T))) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i)
        + (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
              (d := d) (N := N) μ w).Polymer,
            (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ w).activity (X i)
        - (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g S)).Polymer,
            (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g S)) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g S)).activity (X i)
        - (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g T)).Polymer,
            (KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ (deformWeight w g T)) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g T)).activity (X i)) := by
        rw [Summable.tsum_sub ((h1.add h2).sub h3) h4,
          Summable.tsum_sub (h1.add h2) h3, Summable.tsum_add h1 h2]
    _ = ∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
            (weightedLatticePolymerSystem
              (d := d) (N := N) μ w).Polymer)).filter
            (fun X => (∃ i, ¬ Disjoint (X i).1 S) ∧
              (∃ i, ¬ Disjoint (X i).1 T)),
          ((KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i)
            + (KP.ursell (weightedLatticePolymerSystem
                (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ w).activity (X i)
            - (KP.ursell (weightedLatticePolymerSystem
                (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g S)).activity (X i)
            - (KP.ursell (weightedLatticePolymerSystem
                (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g T)).activity (X i)) :=
      tsum_congr fun n => cluster_layer_inclusion_exclusion μ w g S T n

set_option maxHeartbeats 1600000 in
open Classical in
/-- **THE COVARIANCE IDENTITY (B2, W4b):**
`Z[FG]·Z = Z[F]·Z[G]·exp(connecting cluster sum)` — the truncated
correlation of two multiplicative local observables is controlled by
the cluster sum over tuples connecting their supports, under
volume-uniform smallness at the deformed bound
`δ' = δ_w + δ_g + δ_w·δ_g`. -/
theorem covariance_identity
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hlocw : IsLocalWeight (d := d) (N := N) (G := G) w)
    (hlocg : IsLocalWeight (d := d) (N := N) (G := G) g)
    (hmeasw : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    (hmeasg : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => g A p))
    {δw δg : ℝ} (hδw0 : 0 ≤ δw) (hδg0 : 0 ≤ δg)
    (hbdw : ∀ A p, |w A p| ≤ δw) (hbdg : ∀ A p, |g A p| ≤ δg)
    (S T : Finset (ConcretePlaquette d N))
    (t : ℝ) (ht0 : 0 ≤ t)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((δw + δg + δw * δg) * Real.exp t) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      (((δw + δg + δw * δg) * Real.exp t) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((δw + δg + δw * δg) * Real.exp t))) ≤ t) :
    ((weightedPartition (d := d) (N := N) μ
        (deformWeight w g (S ∪ T)) : ℝ) : ℂ) *
      ((weightedPartition (d := d) (N := N) μ w : ℝ) : ℂ)
    = ((weightedPartition (d := d) (N := N) μ
        (deformWeight w g S) : ℝ) : ℂ) *
      ((weightedPartition (d := d) (N := N) μ
        (deformWeight w g T) : ℝ) : ℂ) *
      Complex.exp (∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
            (weightedLatticePolymerSystem
              (d := d) (N := N) μ w).Polymer)).filter
            (fun X => (∃ i, ¬ Disjoint (X i).1 S) ∧
              (∃ i, ¬ Disjoint (X i).1 T)),
          ((KP.ursell (weightedLatticePolymerSystem
              (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i)
            + (KP.ursell (weightedLatticePolymerSystem
                (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ w).activity (X i)
            - (KP.ursell (weightedLatticePolymerSystem
                (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g S)).activity (X i)
            - (KP.ursell (weightedLatticePolymerSystem
                (d := d) (N := N) μ w) X : ℂ) *
              ∏ i, (weightedLatticePolymerSystem
                (d := d) (N := N) μ (deformWeight w g T)).activity (X i))) := by
  classical
  set δ' : ℝ := δw + δg + δw * δg with hδ'def
  have hδ'0 : (0 : ℝ) ≤ δ' := by rw [hδ'def]; positivity
  have hwle : ∀ A p, |w A p| ≤ δ' := fun A p =>
    le_trans (hbdw A p) (by rw [hδ'def]; nlinarith)
  have hbdU : ∀ A p, |deformWeight w g (S ∪ T) A p| ≤ δ' :=
    fun A p => abs_deformWeight_le hbdw hbdg (S ∪ T) A p
  have hbdS : ∀ A p, |deformWeight w g S A p| ≤ δ' :=
    fun A p => abs_deformWeight_le hbdw hbdg S A p
  have hbdT : ∀ A p, |deformWeight w g T A p| ≤ δ' :=
    fun A p => abs_deformWeight_le hbdw hbdg T A p
  -- the four exponential identities
  have e1 := weightedPartition_eq_exp_clusterSum μ
    (isLocalWeight_deformWeight hlocw hlocg (S ∪ T))
    (measurable_deformWeight hmeasw hmeasg (S ∪ T))
    hδ'0 hbdU t ht0 hr hsmall
  have e2 := weightedPartition_eq_exp_clusterSum μ
    hlocw hmeasw hδ'0 hwle t ht0 hr hsmall
  have e3 := weightedPartition_eq_exp_clusterSum μ
    (isLocalWeight_deformWeight hlocw hlocg S)
    (measurable_deformWeight hmeasw hmeasg S)
    hδ'0 hbdS t ht0 hr hsmall
  have e4 := weightedPartition_eq_exp_clusterSum μ
    (isLocalWeight_deformWeight hlocw hlocg T)
    (measurable_deformWeight hmeasw hmeasg T)
    hδ'0 hbdT t ht0 hr hsmall
  -- the four summabilities
  have hs1 : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g (S ∪ T))).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g (S ∪ T))) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g (S ∪ T))).activity (X i)) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => KP.norm_clusterTerm_le _ n)
      (KP.kp_clusterWeight_summable_sharp _
        (weightedLatticePolymerSystem_kpCriterion_volumeUniform
          μ hδ'0 hbdU t ht0 hr hsmall)))
  have hs2 : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ w) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ w).activity (X i)) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => KP.norm_clusterTerm_le _ n)
      (KP.kp_clusterWeight_summable_sharp _
        (weightedLatticePolymerSystem_kpCriterion_volumeUniform
          μ hδ'0 hwle t ht0 hr hsmall)))
  have hs3 : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g S)).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g S)) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g S)).activity (X i)) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => KP.norm_clusterTerm_le _ n)
      (KP.kp_clusterWeight_summable_sharp _
        (weightedLatticePolymerSystem_kpCriterion_volumeUniform
          μ hδ'0 hbdS t ht0 hr hsmall)))
  have hs4 : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g T)).Polymer,
        (KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ (deformWeight w g T)) X : ℂ) *
          ∏ i, (weightedLatticePolymerSystem
            (d := d) (N := N) μ (deformWeight w g T)).activity (X i)) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => KP.norm_clusterTerm_le _ n)
      (KP.kp_clusterWeight_summable_sharp _
        (weightedLatticePolymerSystem_kpCriterion_volumeUniform
          μ hδ'0 hbdT t ht0 hr hsmall)))
  rw [e1, e2, e3, e4, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add,
    ← clusterSum_inclusion_exclusion μ w g S T hs1 hs2 hs3 hs4]
  congr 1
  ring

/-! ### W4d: the decay engine for the weighted gas -/

set_option maxHeartbeats 1600000 in
open Classical in
/-- **The volume-uniform KP criterion for the TILTED weighted gas** —
the tilt and the weight combine into the exponent `t + ε`; transport
of the Wilson-gas tilted criterion with `x := δ·e^{t+ε}`. -/
theorem weightedLatticePolymerSystem_tilt_kpCriterion_volumeUniform
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hbd : ∀ A p, |w A p| ≤ δ)
    (t ε : ℝ) (ht0 : 0 ≤ t)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (t + ε)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((δ * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (t + ε)))) ≤ t) :
    KPCriterion
      ((weightedLatticePolymerSystem (d := d) (N := N) μ w).tilt
        (fun c => ε * (c.1.card : ℝ)))
      (fun c => t * (c.1.card : ℝ)) := by
  classical
  set x : ℝ := δ * Real.exp (t + ε) with hxdef
  have hx : (0 : ℝ) ≤ x := mul_nonneg hδ0 (Real.exp_pos _).le
  set S : ℝ := x / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x) with hSdef
  have hden : (0 : ℝ) < 1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x := by
    rw [hxdef]; linarith
  have hS0 : (0 : ℝ) ≤ S := div_nonneg hx hden.le
  have hthrough : ∀ p : ConcretePlaquette d N,
      (∑ Y ∈ (Finset.univ :
        Finset (weightedLatticePolymerSystem (d := d) (N := N)
          μ w).Polymer).filter (fun Y => p ∈ Y.1),
        x ^ Y.1.card) ≤ S := by
    intro p
    have h := sum_connectedPolymers_through_le (d := d) (N := N) p x hx
      (by rw [hxdef] at *; exact hr)
    convert h using 2
  constructor
  · intro c
    positivity
  · intro c
    have hterm : ∀ Y : (weightedLatticePolymerSystem (d := d) (N := N)
        μ w).Polymer,
        ‖((weightedLatticePolymerSystem (d := d) (N := N) μ w).tilt
            (fun c => ε * (c.1.card : ℝ))).activity Y‖ *
          Real.exp (t * (Y.1.card : ℝ)) ≤ x ^ Y.1.card := by
      intro Y
      have h1 := norm_weightedLatticePolymerSystem_activity_le
        (d := d) (N := N) μ hbd Y
      have h2 : Real.exp ((t + ε) * (Y.1.card : ℝ))
          = Real.exp (t + ε) ^ Y.1.card := by
        rw [mul_comm, ← Real.exp_nat_mul]
      have hcomb : Real.exp (ε * (Y.1.card : ℝ)) *
          Real.exp (t * (Y.1.card : ℝ))
          = Real.exp ((t + ε) * (Y.1.card : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [KP.tilt_norm_activity]
      calc Real.exp (ε * (Y.1.card : ℝ)) *
            ‖(weightedLatticePolymerSystem (d := d) (N := N)
              μ w).activity Y‖ * Real.exp (t * (Y.1.card : ℝ))
          = ‖(weightedLatticePolymerSystem (d := d) (N := N)
              μ w).activity Y‖ *
              (Real.exp (ε * (Y.1.card : ℝ)) *
                Real.exp (t * (Y.1.card : ℝ))) := by ring
        _ = ‖(weightedLatticePolymerSystem (d := d) (N := N)
              μ w).activity Y‖ *
              Real.exp (t + ε) ^ Y.1.card := by rw [hcomb, h2]
        _ ≤ δ ^ Y.1.card * Real.exp (t + ε) ^ Y.1.card :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = x ^ Y.1.card := by rw [hxdef, mul_pow]
    have hdom : ∀ Y ∈ (Finset.univ :
        Finset (weightedLatticePolymerSystem (d := d) (N := N)
          μ w).Polymer).filter
        (fun Y => (weightedLatticePolymerSystem (d := d) (N := N)
          μ w).incomp c Y),
        x ^ Y.1.card ≤ ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q p),
          (if p ∈ Y.1 then x ^ Y.1.card else 0) := by
      intro Y hY
      rw [Finset.mem_filter] at hY
      have hinc : ¬ Disjoint (c.1.biUnion plaquetteSupport)
          (Y.1.biUnion plaquetteSupport) := hY.2
      obtain ⟨e, hec, heY⟩ := Finset.not_disjoint_iff.mp hinc
      obtain ⟨q₀, hq₀, heq₀⟩ := Finset.mem_biUnion.mp hec
      obtain ⟨p₀, hp₀, hep₀⟩ := Finset.mem_biUnion.mp heY
      have htouch : plaquetteTouches q₀ p₀ := fun hd =>
        (Finset.disjoint_left.mp hd heq₀) hep₀
      have hp₀mem : p₀ ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q₀ p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, htouch⟩
      have hinner : x ^ Y.1.card ≤ ∑ p ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q₀ p),
          (if p ∈ Y.1 then x ^ Y.1.card else 0) := by
        have h := Finset.single_le_sum
          (f := fun p => if p ∈ Y.1 then x ^ Y.1.card else 0)
          (fun p _ => by positivity) hp₀mem
        simp only [hp₀, if_true] at h
        exact h
      refine le_trans hinner ?_
      exact Finset.single_le_sum
        (f := fun q => ∑ p ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q p),
          (if p ∈ Y.1 then x ^ Y.1.card else 0))
        (fun q _ => Finset.sum_nonneg fun p _ => by positivity) hq₀
    calc ∑ Y ∈ (Finset.univ :
          Finset (weightedLatticePolymerSystem (d := d) (N := N)
            μ w).Polymer).filter
          (fun Y => (weightedLatticePolymerSystem (d := d) (N := N)
            μ w).incomp c Y),
          ‖((weightedLatticePolymerSystem (d := d) (N := N) μ w).tilt
              (fun c => ε * (c.1.card : ℝ))).activity Y‖ *
            Real.exp (t * (Y.1.card : ℝ))
        ≤ ∑ Y ∈ (Finset.univ :
            Finset (weightedLatticePolymerSystem (d := d) (N := N)
              μ w).Polymer).filter
            (fun Y => (weightedLatticePolymerSystem (d := d) (N := N)
              μ w).incomp c Y),
            x ^ Y.1.card :=
          Finset.sum_le_sum fun Y _ => hterm Y
      _ ≤ ∑ Y ∈ (Finset.univ :
            Finset (weightedLatticePolymerSystem (d := d) (N := N)
              μ w).Polymer).filter
            (fun Y => (weightedLatticePolymerSystem (d := d) (N := N)
              μ w).incomp c Y),
            ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
              Finset (ConcretePlaquette d N)).filter
                (fun p => plaquetteTouches q p),
              (if p ∈ Y.1 then x ^ Y.1.card else 0) :=
          Finset.sum_le_sum hdom
      _ ≤ ∑ Y ∈ (Finset.univ :
            Finset (weightedLatticePolymerSystem (d := d) (N := N)
              μ w).Polymer),
            ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
              Finset (ConcretePlaquette d N)).filter
                (fun p => plaquetteTouches q p),
              (if p ∈ Y.1 then x ^ Y.1.card else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun Y _ _ => Finset.sum_nonneg fun q _ =>
              Finset.sum_nonneg fun p _ => by positivity)
      _ = ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
              (fun p => plaquetteTouches q p),
            ∑ Y ∈ (Finset.univ :
              Finset (weightedLatticePolymerSystem (d := d) (N := N)
                μ w).Polymer),
              (if p ∈ Y.1 then x ^ Y.1.card else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
      _ = ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
              (fun p => plaquetteTouches q p),
            ∑ Y ∈ (Finset.univ :
              Finset (weightedLatticePolymerSystem (d := d) (N := N)
                μ w).Polymer).filter (fun Y => p ∈ Y.1),
              x ^ Y.1.card := by
          refine Finset.sum_congr rfl fun q _ => ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          exact (Finset.sum_filter _ _).symm
      _ ≤ ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
              (fun p => plaquetteTouches q p), S := by
          refine Finset.sum_le_sum fun q _ => ?_
          exact Finset.sum_le_sum fun p _ => hthrough p
      _ ≤ ∑ q ∈ c.1, ((16 * d : ℕ) : ℝ) * S := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hS0
          exact_mod_cast card_plaquettesTouching_le q
      _ = (c.1.card : ℝ) * (((16 * d : ℕ) : ℝ) * S) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (c.1.card : ℝ) * t := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hSdef, hxdef]
          exact hsmall
      _ = t * (c.1.card : ℝ) := mul_comm _ _

open Classical in
/-- `cluster_dist_le`, weighted-gas form: the geometry is
weight-independent, so the Wilson-gas statement applies by defeq at a
dummy energy. -/
theorem weighted_cluster_dist_le
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ) {n : ℕ}
    {X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer}
    (hX : KP.IsCluster
      (weightedLatticePolymerSystem (d := d) (N := N) μ w) X)
    {i₀ j₀ : Fin n} {p q : ConcretePlaquette d N}
    (hp : p ∈ (X i₀).1) (hq : q ∈ (X j₀).1) :
    (touchGraph d N).dist p q ≤ 2 * ∑ i, (X i).1.card :=
  cluster_dist_le μ (fun _ => (0 : ℝ)) 0 (X := X) hX hp hq

set_option maxHeartbeats 800000 in
open Classical in
/-- **Connecting-sum domination for the weighted gas** — transport of
`connecting_pinned_le_GE`. -/
lemma weighted_connecting_pinned_le_GE
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    {p q : ConcretePlaquette d N}
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer)
    (hp : p ∈ c.1) (n : ℕ) :
    (((n + 1).factorial : ℝ))⁻¹ *
      ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
        (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).Polymer)).filter
        (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
        |((KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ w) X : ℤ) : ℝ)| *
          ∏ i, ‖(weightedLatticePolymerSystem
            (d := d) (N := N) μ w).activity (X i)‖
    ≤ KP.pinnedClusterWeightGE (weightedLatticePolymerSystem
        (d := d) (N := N) μ w)
        (fun c' => c'.1.card) c ((touchGraph d N).dist p q / 2) n := by
  classical
  unfold KP.pinnedClusterWeightGE
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [show ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
      (weightedLatticePolymerSystem
        (d := d) (N := N) μ w).Polymer)).filter
      (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
      |((KP.ursell (weightedLatticePolymerSystem
        (d := d) (N := N) μ w) X : ℤ) : ℝ)| *
        ∏ i, ‖(weightedLatticePolymerSystem
          (d := d) (N := N) μ w).activity (X i)‖
    = ∑ X ∈ ((Finset.univ : Finset (Fin (n + 1) →
        (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).Polymer)).filter
        (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1)).filter
        (fun X => KP.IsCluster (weightedLatticePolymerSystem
          (d := d) (N := N) μ w) X),
        |((KP.ursell (weightedLatticePolymerSystem
          (d := d) (N := N) μ w) X : ℤ) : ℝ)| *
          ∏ i, ‖(weightedLatticePolymerSystem
            (d := d) (N := N) μ w).activity (X i)‖
    from (Finset.sum_filter_of_ne fun X _ hne => by
      by_contra hnc
      exact hne (by
        rw [KP.ursell_eq_zero_of_not_isCluster _ X hnc]
        simp)).symm]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun X _ _ =>
    mul_nonneg (abs_nonneg _)
      (Finset.prod_nonneg fun i _ => norm_nonneg _)
  intro X hX
  rw [Finset.mem_filter, Finset.mem_filter] at hX
  obtain ⟨⟨-, hX0, j, hqj⟩, hclus⟩ := hX
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hX0, ?_⟩
  have hp0 : p ∈ (X 0).1 := by rw [hX0]; exact hp
  have hdist := weighted_cluster_dist_le μ w hclus hp0 hqj
  have hsz : ∑ i, (fun c' : (weightedLatticePolymerSystem
      (d := d) (N := N) μ w).Polymer => c'.1.card) (X i)
      = ∑ i, (X i).1.card := rfl
  omega

set_option maxHeartbeats 1600000 in
open Classical in
/-- **THE CONNECTING-CLUSTER DECAY for the weighted gas
(volume-uniform):** transport of `connecting_cluster_decay` with
`x := δ·e^{t+ε}`. -/
theorem weighted_connecting_cluster_decay
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hbd : ∀ A p, |w A p| ≤ δ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (t + ε)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((δ * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (t + ε)))) ≤ t)
    (p q : ConcretePlaquette d N) :
    ∑ c ∈ (Finset.univ : Finset (weightedLatticePolymerSystem
        (d := d) (N := N) μ w).Polymer).filter
        (fun c => p ∈ c.1),
      ∑' n : ℕ, (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
          (weightedLatticePolymerSystem
            (d := d) (N := N) μ w).Polymer)).filter
          (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
          |((KP.ursell (weightedLatticePolymerSystem
            (d := d) (N := N) μ w) X : ℤ) : ℝ)| *
            ∏ i, ‖(weightedLatticePolymerSystem
              (d := d) (N := N) μ w).activity (X i)‖
    ≤ Real.exp (-(ε * (((touchGraph d N).dist p q / 2 : ℕ) : ℝ))) *
        ((δ * Real.exp (t + ε)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (t + ε)))) := by
  classical
  set L : ℕ := (touchGraph d N).dist p q / 2 with hL
  set x : ℝ := δ * Real.exp (t + ε) with hxdef
  have hx : (0 : ℝ) ≤ x := mul_nonneg hδ0 (Real.exp_pos _).le
  have hcrit := weightedLatticePolymerSystem_tilt_kpCriterion_volumeUniform
    (d := d) (N := N) μ hδ0 hbd t ε ht0 hr hsmall
  have hper : ∀ c ∈ (Finset.univ : Finset (weightedLatticePolymerSystem
      (d := d) (N := N) μ w).Polymer).filter (fun c => p ∈ c.1),
      (∑' n : ℕ, (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
          (weightedLatticePolymerSystem
            (d := d) (N := N) μ w).Polymer)).filter
          (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
          |((KP.ursell (weightedLatticePolymerSystem
            (d := d) (N := N) μ w) X : ℤ) : ℝ)| *
            ∏ i, ‖(weightedLatticePolymerSystem
              (d := d) (N := N) μ w).activity (X i)‖)
      ≤ Real.exp (-(ε * L)) *
          (Real.exp (ε * (c.1.card : ℝ)) *
            ‖(weightedLatticePolymerSystem
              (d := d) (N := N) μ w).activity c‖ *
            Real.exp (t * (c.1.card : ℝ))) := by
    intro c hc
    have hpc := (Finset.mem_filter.mp hc).2
    have htail := KP.pinned_cluster_tail_summable
      (weightedLatticePolymerSystem (d := d) (N := N) μ w)
      (fun c' => c'.1.card) hε0 hcrit c L
    have hterm := fun n => weighted_connecting_pinned_le_GE
      (q := q) μ w c hpc n
    have hnn : ∀ n : ℕ, 0 ≤ (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
          (weightedLatticePolymerSystem
            (d := d) (N := N) μ w).Polymer)).filter
          (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
          |((KP.ursell (weightedLatticePolymerSystem
            (d := d) (N := N) μ w) X : ℤ) : ℝ)| *
            ∏ i, ‖(weightedLatticePolymerSystem
              (d := d) (N := N) μ w).activity (X i)‖ := by
      intro n
      refine mul_nonneg (by positivity)
        (Finset.sum_nonneg fun X _ => mul_nonneg (abs_nonneg _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _))
    have hsumm : Summable (fun n : ℕ =>
        (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
          (weightedLatticePolymerSystem
            (d := d) (N := N) μ w).Polymer)).filter
          (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
          |((KP.ursell (weightedLatticePolymerSystem
            (d := d) (N := N) μ w) X : ℤ) : ℝ)| *
            ∏ i, ‖(weightedLatticePolymerSystem
              (d := d) (N := N) μ w).activity (X i)‖) :=
      Summable.of_nonneg_of_le hnn hterm htail.1
    exact le_trans
      (Summable.tsum_le_tsum hterm hsumm htail.1) htail.2
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  calc ∑ c ∈ (Finset.univ : Finset (weightedLatticePolymerSystem
        (d := d) (N := N) μ w).Polymer).filter
        (fun c => p ∈ c.1),
        Real.exp (ε * (c.1.card : ℝ)) *
          ‖(weightedLatticePolymerSystem
            (d := d) (N := N) μ w).activity c‖ *
          Real.exp (t * (c.1.card : ℝ))
      ≤ ∑ c ∈ (Finset.univ : Finset (weightedLatticePolymerSystem
          (d := d) (N := N) μ w).Polymer).filter
          (fun c => p ∈ c.1),
          x ^ c.1.card := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 := norm_weightedLatticePolymerSystem_activity_le
          (d := d) (N := N) μ hbd c
        have h2 : Real.exp ((t + ε) * (c.1.card : ℝ))
            = Real.exp (t + ε) ^ c.1.card := by
          rw [mul_comm, ← Real.exp_nat_mul]
        have hcomb : Real.exp (ε * (c.1.card : ℝ)) *
            Real.exp (t * (c.1.card : ℝ))
            = Real.exp ((t + ε) * (c.1.card : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc Real.exp (ε * (c.1.card : ℝ)) *
            ‖(weightedLatticePolymerSystem
              (d := d) (N := N) μ w).activity c‖ *
            Real.exp (t * (c.1.card : ℝ))
            = ‖(weightedLatticePolymerSystem
                (d := d) (N := N) μ w).activity c‖ *
              (Real.exp (ε * (c.1.card : ℝ)) *
                Real.exp (t * (c.1.card : ℝ))) := by ring
          _ = ‖(weightedLatticePolymerSystem
                (d := d) (N := N) μ w).activity c‖ *
              Real.exp (t + ε) ^ c.1.card := by rw [hcomb, h2]
          _ ≤ δ ^ c.1.card * Real.exp (t + ε) ^ c.1.card :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = x ^ c.1.card := by rw [hxdef, mul_pow]
    _ ≤ x / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x) := by
        have h := sum_connectedPolymers_through_le (d := d) (N := N)
          p x hx (by rw [hxdef] at *; exact hr)
        convert h using 2

set_option maxHeartbeats 1600000 in
open Classical in
/-- **The symmetrization bound (B4):** the tuple sum over an
anywhere-pinned connecting filter is at most `(n+1)` times the
position-0-pinned tuple sum.  Precompose with the transposition
`swap 0 i`: the Ursell coefficient (`ursell_comp_equiv`) and the
activity product (`Equiv.prod_comp`) are relabeling-invariant, and the
second existential is permutation-stable. -/
lemma sum_connecting_le_succ_mul_pinned (P : KP.PolymerSystem)
    [Fintype P.Polymer] (Q R : P.Polymer → Prop) (n : ℕ) :
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X => (∃ i, Q (X i)) ∧ (∃ j, R (X j))),
      |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖
    ≤ ((n + 1 : ℕ) : ℝ) *
      ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X => Q (X 0) ∧ (∃ j, R (X j))),
        |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ := by
  classical
  have hF0 : ∀ X : Fin (n + 1) → P.Polymer,
      0 ≤ |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ :=
    fun X => mul_nonneg (abs_nonneg _)
      (Finset.prod_nonneg fun k _ => norm_nonneg _)
  have hite0 : ∀ (X : Fin (n + 1) → P.Polymer) (i : Fin (n + 1)),
      0 ≤ (if Q (X i) ∧ (∃ j, R (X j)) then
        |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ else 0) := by
    intro X i
    by_cases h : Q (X i) ∧ (∃ j, R (X j))
    · rw [if_pos h]
      exact hF0 X
    · rw [if_neg h]
  have hswap : ∀ i : Fin (n + 1),
      (∑ X : Fin (n + 1) → P.Polymer,
        if Q (X i) ∧ (∃ j, R (X j)) then
          |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ else 0)
      = ∑ X : Fin (n + 1) → P.Polymer,
        if Q (X 0) ∧ (∃ j, R (X j)) then
          |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ else 0 := by
    intro i
    have hbij : Function.Bijective
        (fun X : Fin (n + 1) → P.Polymer => X ∘ Equiv.swap 0 i) := by
      have hinv : Function.Involutive
          (fun X : Fin (n + 1) → P.Polymer => X ∘ Equiv.swap 0 i) := by
        intro X
        funext k
        simp [Function.comp, Equiv.swap_apply_self]
      exact hinv.bijective
    refine Fintype.sum_bijective _ hbij _ _ ?_
    intro X
    have hc0 : (X ∘ Equiv.swap 0 i) 0 = X i := by
      simp [Function.comp, Equiv.swap_apply_left]
    have hex : (∃ j, R ((X ∘ Equiv.swap 0 i) j)) ↔ ∃ j, R (X j) := by
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨Equiv.swap 0 i j, hj⟩
      · rintro ⟨j, hj⟩
        refine ⟨Equiv.swap 0 i j, ?_⟩
        simpa [Function.comp, Equiv.swap_apply_self] using hj
    have hu : KP.ursell P (X ∘ Equiv.swap 0 i) = KP.ursell P X :=
      KP.ursell_comp_equiv P X (Equiv.swap 0 i)
    have hprod : (∏ k, ‖P.activity ((X ∘ Equiv.swap 0 i) k)‖)
        = ∏ k, ‖P.activity (X k)‖ :=
      Equiv.prod_comp (Equiv.swap 0 i) (fun k => ‖P.activity (X k)‖)
    refine (if_congr (and_congr (by rw [hc0]) hex) ?_ rfl).symm
    rw [hu, hprod]
  calc ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X => (∃ i, Q (X i)) ∧ (∃ j, R (X j))),
        |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖
      ≤ ∑ X : Fin (n + 1) → P.Polymer, ∑ i : Fin (n + 1),
        (if Q (X i) ∧ (∃ j, R (X j)) then
          |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ else 0) := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun X _ => ?_
        by_cases hX : (∃ i, Q (X i)) ∧ (∃ j, R (X j))
        · rw [if_pos hX]
          obtain ⟨⟨i₀, hi₀⟩, hT⟩ := hX
          have h := Finset.single_le_sum
            (f := fun i => if Q (X i) ∧ (∃ j, R (X j)) then
              |((KP.ursell P X : ℤ) : ℝ)| *
                ∏ k, ‖P.activity (X k)‖ else 0)
            (fun i _ => hite0 X i) (Finset.mem_univ i₀)
          have h' : (if Q (X i₀) ∧ (∃ j, R (X j)) then
              |((KP.ursell P X : ℤ) : ℝ)| *
                ∏ k, ‖P.activity (X k)‖ else 0)
              ≤ ∑ i : Fin (n + 1),
                (if Q (X i) ∧ (∃ j, R (X j)) then
                  |((KP.ursell P X : ℤ) : ℝ)| *
                    ∏ k, ‖P.activity (X k)‖ else 0) := h
          rw [if_pos ⟨hi₀, hT⟩] at h'
          exact h'
        · rw [if_neg hX]
          exact Finset.sum_nonneg fun i _ => hite0 X i
    _ = ∑ i : Fin (n + 1), ∑ X : Fin (n + 1) → P.Polymer,
        (if Q (X i) ∧ (∃ j, R (X j)) then
          |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ else 0) :=
        Finset.sum_comm
    _ = ∑ _i : Fin (n + 1), ∑ X : Fin (n + 1) → P.Polymer,
        (if Q (X 0) ∧ (∃ j, R (X j)) then
          |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ else 0) :=
        Finset.sum_congr rfl fun i _ => hswap i
    _ = ((n + 1 : ℕ) : ℝ) * ∑ X : Fin (n + 1) → P.Polymer,
        (if Q (X 0) ∧ (∃ j, R (X j)) then
          |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ else 0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ = ((n + 1 : ℕ) : ℝ) *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => Q (X 0) ∧ (∃ j, R (X j))),
          |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ := by
        rw [Finset.sum_filter]

end YangMills
