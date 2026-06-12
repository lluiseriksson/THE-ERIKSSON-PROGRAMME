/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Basic
import YangMills.KP.Criterion
import YangMills.KP.KPBound
import YangMills.L1_GibbsMeasure.PolymerFactorization

/-!
# The lattice polymer system

Instantiates the abstract `PolymerSystem` (the interface of the verified
Kotecký–Preiss machinery) with the **actual lattice gas** produced by the
high-temperature expansion: polymers are nonempty plaquette sets, two
polymers are incompatible when their edge supports overlap, and the activity
of a polymer is the gauge expectation of its Mayer-weight product.

Proved here: the structure axioms (hard-core self-incompatibility from
nonemptiness of supports, symmetry), a `Fintype` instance, and the
**activity bound** `‖z(c)‖ ≤ (e^{|β|B} − 1)^{|c|}` for bounded plaquette
energies — geometric smallness in the polymer size at small coupling.

By `integral_prod_prod_plaquetteWeight_of_pairwiseDisjoint`, activities are
multiplicative over support-disjoint families, so this system genuinely
carries the polymer-gas structure of the expansion.  Remaining toward
lattice KP convergence: the `KPCriterion` entropy estimate (next campaign;
honest note — a volume-uniform criterion requires restricting polymers to
*connected* plaquette sets).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory KP

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-- The **lattice polymer system** of the high-temperature expansion:
nonempty plaquette sets, support-overlap incompatibility, gauge-expectation
activities. -/
noncomputable def latticePolymerSystem (μ : Measure G) (pe : G → ℝ) (β : ℝ) :
    PolymerSystem where
  Polymer := { c : Finset (ConcretePlaquette d N) // c.Nonempty }
  incomp c c' := ¬ Disjoint (c.1.biUnion plaquetteSupport)
    (c'.1.biUnion plaquetteSupport)
  incomp_symm := by
    intro a b h hd
    exact h hd.symm
  incomp_self := by
    intro c hdisj
    obtain ⟨p, hp⟩ := c.2
    have hmem : (p.edges 0).pos ∈ c.1.biUnion plaquetteSupport :=
      Finset.mem_biUnion.mpr ⟨p, hp, by simp [plaquetteSupport]⟩
    exact (Finset.disjoint_left.mp hdisj hmem) hmem
  activity c := ((∫ A, ∏ p ∈ c.1, plaquetteWeight pe β A p
    ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)

instance (μ : Measure G) (pe : G → ℝ) (β : ℝ) :
    Fintype (latticePolymerSystem (d := d) (N := N) μ pe β).Polymer :=
  inferInstanceAs (Fintype { c : Finset (ConcretePlaquette d N) // c.Nonempty })

/-- **Activity smallness for the lattice polymer gas:**
`‖z(c)‖ ≤ (e^{|β|B} − 1)^{|c|}` — geometrically small in the polymer size at
small coupling, the input shape of the KP criterion. -/
theorem norm_latticePolymerSystem_activity_le
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (c : { c : Finset (ConcretePlaquette d N) // c.Nonempty }) :
    ‖(latticePolymerSystem (d := d) (N := N) μ pe β).activity c‖
      ≤ (Real.exp (|β| * B) - 1) ^ c.1.card := by
  show ‖((∫ A, ∏ p ∈ c.1, plaquetteWeight pe β A p
    ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hbound := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := gaugeMeasureFrom (d := d) (N := N) μ)
    (f := fun A : GaugeConfig d N G => ∏ p ∈ c.1, plaquetteWeight pe β A p)
    (C := (Real.exp (|β| * B) - 1) ^ c.1.card) ?_
  · rw [Real.norm_eq_abs] at hbound
    simpa [measure_univ] using hbound
  · refine MeasureTheory.ae_of_all _ fun A => ?_
    rw [Real.norm_eq_abs, Finset.abs_prod]
    calc ∏ p ∈ c.1, |plaquetteWeight pe β A p|
        ≤ ∏ _p ∈ c.1, (Real.exp (|β| * B) - 1) :=
          Finset.prod_le_prod (fun p _ => abs_nonneg _)
            (fun p _ => abs_plaquetteWeight_le pe β A p hpe)
      _ = (Real.exp (|β| * B) - 1) ^ c.1.card := by
          rw [Finset.prod_const]

/-- Binomial subset-counting: `∑_{c ⊆ univ} x^{|c|} = (x+1)^{#X}`. -/
lemma sum_powerset_pow_card {X : Type*} [Fintype X] [DecidableEq X] (x : ℝ) :
    ∑ c ∈ (Finset.univ : Finset X).powerset, x ^ c.card
      = (x + 1) ^ Fintype.card X := by
  rw [← Finset.card_univ, ← Finset.prod_const (x + 1), Finset.prod_add]
  exact Finset.sum_congr rfl fun t _ => by
    rw [Finset.prod_const, Finset.prod_const_one, mul_one]

/-- **The KP criterion holds for the lattice polymer gas at small coupling**
(finite volume, weight `a(c) = |c|`): if the total weighted activity over
*all* polymers — bounded via the binomial entropy by
`(1 + (e^{|β|B}−1)·e)^{#plaquettes} − 1` — is at most `1`, then the
Kotecký–Preiss smallness criterion is satisfied.  The hypothesis `hsmall`
holds for `β` small (volume-dependently); the volume-uniform refinement
requires restricting to connected polymers (documented in
`docs/DEPENDENCY-GRAPH.md`). -/
theorem latticePolymerSystem_kpCriterion
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (hsmall : ((Real.exp (|β| * B) - 1) * Real.exp 1 + 1)
        ^ Fintype.card (ConcretePlaquette d N) - 1 ≤ 1) :
    KPCriterion (latticePolymerSystem (d := d) (N := N) μ pe β)
      (fun c => (c.1.card : ℝ)) := by
  classical
  have hε0 : (0 : ℝ) ≤ Real.exp (|β| * B) - 1 := by
    have : (1 : ℝ) ≤ Real.exp (|β| * B) := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      have hB : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hpe 1)
      positivity
    linarith
  constructor
  · intro c
    positivity
  · intro c
    -- bound each term by `((e^{|β|B}−1)·e)^{|Y|}` and extend to all polymers
    have hterm : ∀ Y : { c : Finset (ConcretePlaquette d N) // c.Nonempty },
        ‖(latticePolymerSystem (d := d) (N := N) μ pe β).activity Y‖ *
          Real.exp ((Y.1.card : ℝ))
        ≤ ((Real.exp (|β| * B) - 1) * Real.exp 1) ^ Y.1.card := by
      intro Y
      have h1 := norm_latticePolymerSystem_activity_le
        (d := d) (N := N) μ hpe β Y
      have h2 : Real.exp ((Y.1.card : ℝ)) = Real.exp 1 ^ Y.1.card := by
        rw [← Real.exp_nat_mul, mul_one]
      rw [h2, mul_pow]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    calc ∑ Y ∈ Finset.univ.filter
          (fun Y => (latticePolymerSystem (d := d) (N := N) μ pe β).incomp c Y),
          ‖(latticePolymerSystem (d := d) (N := N) μ pe β).activity Y‖ *
            Real.exp ((Y.1.card : ℝ))
        ≤ ∑ Y : { c : Finset (ConcretePlaquette d N) // c.Nonempty },
            ((Real.exp (|β| * B) - 1) * Real.exp 1) ^ Y.1.card := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun Y _ _ =>
              mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)) ?_
          exact Finset.sum_le_sum fun Y _ => hterm Y
      _ = ∑ c' ∈ (Finset.univ :
            Finset (Finset (ConcretePlaquette d N))).filter (·.Nonempty),
            ((Real.exp (|β| * B) - 1) * Real.exp 1) ^ c'.card := by
          exact (Finset.sum_subtype
            ((Finset.univ :
              Finset (Finset (ConcretePlaquette d N))).filter (·.Nonempty))
            (fun c' => by simp)
            (fun c' => ((Real.exp (|β| * B) - 1) * Real.exp 1) ^ c'.card)).symm
      _ ≤ ((Real.exp (|β| * B) - 1) * Real.exp 1 + 1)
            ^ Fintype.card (ConcretePlaquette d N) - 1 := by
          have hfil : (Finset.univ :
              Finset (Finset (ConcretePlaquette d N))).filter (·.Nonempty)
              = (Finset.univ :
                Finset (Finset (ConcretePlaquette d N))).erase ∅ := by
            ext c'
            simp [Finset.nonempty_iff_ne_empty]
          rw [hfil]
          have hsum := Finset.add_sum_erase
            (Finset.univ : Finset (Finset (ConcretePlaquette d N)))
            (fun c' => ((Real.exp (|β| * B) - 1) * Real.exp 1) ^ c'.card)
            (Finset.mem_univ ∅)
          have hbin : ∑ c' ∈ (Finset.univ :
              Finset (Finset (ConcretePlaquette d N))),
              ((Real.exp (|β| * B) - 1) * Real.exp 1) ^ c'.card
              = ((Real.exp (|β| * B) - 1) * Real.exp 1 + 1)
                ^ Fintype.card (ConcretePlaquette d N) := by
            rw [← Finset.powerset_univ]
            exact sum_powerset_pow_card _
          rw [← hbin]
          have := hsum
          simp only [Finset.card_empty, pow_zero] at this
          linarith
      _ ≤ 1 := hsmall
      _ ≤ (c.1.card : ℝ) := by
          have := c.2.card_pos
          exact_mod_cast this

/-- **The KP criterion with scaled weight `a(c) = t·|c|`** — the form whose
maximum `A = t·#plaquettes` can be made small enough to compose with the
closed uniform-smallness KP corollaries. -/
theorem latticePolymerSystem_kpCriterion_scaled
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) (t : ℝ) (ht0 : 0 ≤ t)
    (hsmall : ((Real.exp (|β| * B) - 1) * Real.exp t + 1)
        ^ Fintype.card (ConcretePlaquette d N) - 1 ≤ t) :
    KPCriterion (latticePolymerSystem (d := d) (N := N) μ pe β)
      (fun c => t * (c.1.card : ℝ)) := by
  classical
  have hε0 : (0 : ℝ) ≤ Real.exp (|β| * B) - 1 := by
    have h1 : (1 : ℝ) ≤ Real.exp (|β| * B) := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      have hB : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hpe 1)
      positivity
    linarith
  constructor
  · intro c
    positivity
  · intro c
    have hterm : ∀ Y : { c : Finset (ConcretePlaquette d N) // c.Nonempty },
        ‖(latticePolymerSystem (d := d) (N := N) μ pe β).activity Y‖ *
          Real.exp (t * (Y.1.card : ℝ))
        ≤ ((Real.exp (|β| * B) - 1) * Real.exp t) ^ Y.1.card := by
      intro Y
      have h1 := norm_latticePolymerSystem_activity_le
        (d := d) (N := N) μ hpe β Y
      have h2 : Real.exp (t * (Y.1.card : ℝ)) = Real.exp t ^ Y.1.card := by
        rw [mul_comm, ← Real.exp_nat_mul]
      rw [h2, mul_pow]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    calc ∑ Y ∈ Finset.univ.filter
          (fun Y => (latticePolymerSystem (d := d) (N := N) μ pe β).incomp c Y),
          ‖(latticePolymerSystem (d := d) (N := N) μ pe β).activity Y‖ *
            Real.exp (t * (Y.1.card : ℝ))
        ≤ ∑ Y : { c : Finset (ConcretePlaquette d N) // c.Nonempty },
            ((Real.exp (|β| * B) - 1) * Real.exp t) ^ Y.1.card := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun Y _ _ =>
              mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)) ?_
          exact Finset.sum_le_sum fun Y _ => hterm Y
      _ = ∑ c' ∈ (Finset.univ :
            Finset (Finset (ConcretePlaquette d N))).filter (·.Nonempty),
            ((Real.exp (|β| * B) - 1) * Real.exp t) ^ c'.card := by
          exact (Finset.sum_subtype
            ((Finset.univ :
              Finset (Finset (ConcretePlaquette d N))).filter (·.Nonempty))
            (fun c' => by simp)
            (fun c' => ((Real.exp (|β| * B) - 1) * Real.exp t) ^ c'.card)).symm
      _ ≤ ((Real.exp (|β| * B) - 1) * Real.exp t + 1)
            ^ Fintype.card (ConcretePlaquette d N) - 1 := by
          have hfil : (Finset.univ :
              Finset (Finset (ConcretePlaquette d N))).filter (·.Nonempty)
              = (Finset.univ :
                Finset (Finset (ConcretePlaquette d N))).erase ∅ := by
            ext c'
            simp [Finset.nonempty_iff_ne_empty]
          rw [hfil]
          have hsum := Finset.add_sum_erase
            (Finset.univ : Finset (Finset (ConcretePlaquette d N)))
            (fun c' => ((Real.exp (|β| * B) - 1) * Real.exp t) ^ c'.card)
            (Finset.mem_univ ∅)
          have hbin : ∑ c' ∈ (Finset.univ :
              Finset (Finset (ConcretePlaquette d N))),
              ((Real.exp (|β| * B) - 1) * Real.exp t) ^ c'.card
              = ((Real.exp (|β| * B) - 1) * Real.exp t + 1)
                ^ Fintype.card (ConcretePlaquette d N) := by
            rw [← Finset.powerset_univ]
            exact sum_powerset_pow_card _
          rw [← hbin]
          have hthis := hsum
          simp only [Finset.card_empty, pow_zero] at hthis
          linarith
      _ ≤ t := hsmall
      _ ≤ t * (c.1.card : ℝ) := by
          have hc1 : (1 : ℝ) ≤ (c.1.card : ℝ) := by
            exact_mod_cast c.2.card_pos
          nlinarith

/-- **CONVERGENCE OF THE LATTICE MAYER SERIES (verified, small coupling).**
For `t` satisfying the scaled smallness and `e·t·#plaquettes < 1`, the
cluster-expansion series of the lattice polymer gas is absolutely summable —
the Kotecký–Preiss convergence theorem applied to the physical system. -/
theorem latticeClusterSum_summable
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) (t : ℝ) (ht0 : 0 ≤ t)
    (hsmall : ((Real.exp (|β| * B) - 1) * Real.exp t + 1)
        ^ Fintype.card (ConcretePlaquette d N) - 1 ≤ t)
    (hr : Real.exp 1 *
      (t * (Fintype.card (ConcretePlaquette d N) : ℝ)) < 1) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) →
        (latticePolymerSystem (d := d) (N := N) μ pe β).Polymer,
        (ursell (latticePolymerSystem (d := d) (N := N) μ pe β) X : ℂ) *
          ∏ i, (latticePolymerSystem (d := d) (N := N) μ pe β).activity (X i)) := by
  refine kp_convergence (latticePolymerSystem (d := d) (N := N) μ pe β)
    (latticePolymerSystem_kpCriterion_scaled (d := d) (N := N)
      μ hpe β t ht0 hsmall)
    (A := t * (Fintype.card (ConcretePlaquette d N) : ℝ))
    (by positivity) ?_ hr
  intro c
  have hcard : (c.1.card : ℝ) ≤ (Fintype.card (ConcretePlaquette d N) : ℝ) := by
    exact_mod_cast Finset.card_le_univ c.1
  exact mul_le_mul_of_nonneg_left hcard ht0

/-- **Quantitative KP bound for the lattice gas:**
`‖clusterSum‖ ≤ (∑‖z‖)/(1 − e·t·#plaquettes)` at small coupling. -/
theorem norm_latticeClusterSum_le
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) (t : ℝ) (ht0 : 0 ≤ t)
    (hsmall : ((Real.exp (|β| * B) - 1) * Real.exp t + 1)
        ^ Fintype.card (ConcretePlaquette d N) - 1 ≤ t)
    (hr : Real.exp 1 *
      (t * (Fintype.card (ConcretePlaquette d N) : ℝ)) < 1) :
    ‖clusterSum (latticePolymerSystem (d := d) (N := N) μ pe β)‖
      ≤ (∑ y, ‖(latticePolymerSystem (d := d) (N := N) μ pe β).activity y‖) /
        (1 - Real.exp 1 *
          (t * (Fintype.card (ConcretePlaquette d N) : ℝ))) := by
  refine kp_norm_clusterSum_le (latticePolymerSystem (d := d) (N := N) μ pe β)
    (latticePolymerSystem_kpCriterion_scaled (d := d) (N := N)
      μ hpe β t ht0 hsmall)
    (by positivity) ?_ hr
  intro c
  have hcard : (c.1.card : ℝ) ≤ (Fintype.card (ConcretePlaquette d N) : ℝ) := by
    exact_mod_cast Finset.card_le_univ c.1
  exact mul_le_mul_of_nonneg_left hcard ht0

/-! ### The connected polymer system (the canonical gas) -/

/-- Two plaquettes **touch** when their edge supports intersect. -/
def plaquetteTouches {d N : ℕ} [NeZero N] (p q : ConcretePlaquette d N) :
    Prop :=
  ¬ Disjoint (plaquetteSupport p) (plaquetteSupport q)

/-- A plaquette set is a **connected polymer** when its touching graph is
connected. -/
def IsConnectedPolymer {d N : ℕ} [NeZero N]
    (c : Finset (ConcretePlaquette d N)) : Prop :=
  (SimpleGraph.fromRel (fun p q : ↥c => plaquetteTouches p.1 q.1)).Connected

/-- The **connected lattice polymer system**: polymers are nonempty
*connected* plaquette sets — the canonical gas of the high-temperature
expansion (and the system on which the volume-uniform entropy bound will be
proved). -/
noncomputable def connectedLatticePolymerSystem (μ : Measure G)
    (pe : G → ℝ) (β : ℝ) : PolymerSystem where
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
  activity c := ((∫ A, ∏ p ∈ c.1, plaquetteWeight pe β A p
    ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)

noncomputable instance (μ : Measure G) (pe : G → ℝ) (β : ℝ) :
    Fintype (connectedLatticePolymerSystem (d := d) (N := N) μ pe β).Polymer := by
  classical
  exact inferInstanceAs (Fintype { c : Finset (ConcretePlaquette d N) //
    c.Nonempty ∧ IsConnectedPolymer c })

/-- Activity smallness for the connected gas (same bound). -/
theorem norm_connectedLatticePolymerSystem_activity_le
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (c : { c : Finset (ConcretePlaquette d N) //
      c.Nonempty ∧ IsConnectedPolymer c }) :
    ‖(connectedLatticePolymerSystem (d := d) (N := N) μ pe β).activity c‖
      ≤ (Real.exp (|β| * B) - 1) ^ c.1.card :=
  norm_latticePolymerSystem_activity_le (d := d) (N := N) μ hpe β
    ⟨c.1, c.2.1⟩

/-- **The KP criterion for the connected gas** (scaled weight `a = t·|c|`):
the connected polymers are a subfamily of all polymers, so the same binomial
entropy bound applies a fortiori. -/
theorem connectedLatticePolymerSystem_kpCriterion_scaled
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) (t : ℝ) (ht0 : 0 ≤ t)
    (hsmall : ((Real.exp (|β| * B) - 1) * Real.exp t + 1)
        ^ Fintype.card (ConcretePlaquette d N) - 1 ≤ t) :
    KPCriterion (connectedLatticePolymerSystem (d := d) (N := N) μ pe β)
      (fun c => t * (c.1.card : ℝ)) := by
  classical
  have hε0 : (0 : ℝ) ≤ Real.exp (|β| * B) - 1 := by
    have h1 : (1 : ℝ) ≤ Real.exp (|β| * B) := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      have hB : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hpe 1)
      positivity
    linarith
  constructor
  · intro c
    positivity
  · intro c
    have hterm : ∀ Y : { c : Finset (ConcretePlaquette d N) //
        c.Nonempty ∧ IsConnectedPolymer c },
        ‖(connectedLatticePolymerSystem (d := d) (N := N) μ pe β).activity Y‖ *
          Real.exp (t * (Y.1.card : ℝ))
        ≤ ((Real.exp (|β| * B) - 1) * Real.exp t) ^ Y.1.card := by
      intro Y
      have h1 := norm_connectedLatticePolymerSystem_activity_le
        (d := d) (N := N) μ hpe β Y
      have h2 : Real.exp (t * (Y.1.card : ℝ)) = Real.exp t ^ Y.1.card := by
        rw [mul_comm, ← Real.exp_nat_mul]
      rw [h2, mul_pow]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    calc ∑ Y ∈ Finset.univ.filter (fun Y =>
          (connectedLatticePolymerSystem (d := d) (N := N) μ pe β).incomp c Y),
          ‖(connectedLatticePolymerSystem (d := d) (N := N) μ pe β).activity Y‖ *
            Real.exp (t * (Y.1.card : ℝ))
        ≤ ∑ Y : { c : Finset (ConcretePlaquette d N) //
            c.Nonempty ∧ IsConnectedPolymer c },
            ((Real.exp (|β| * B) - 1) * Real.exp t) ^ Y.1.card := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun Y _ _ =>
              mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)) ?_
          exact Finset.sum_le_sum fun Y _ => hterm Y
      _ = ∑ c' ∈ (Finset.univ :
            Finset (Finset (ConcretePlaquette d N))).filter
              (fun c' => c'.Nonempty ∧ IsConnectedPolymer c'),
            ((Real.exp (|β| * B) - 1) * Real.exp t) ^ c'.card := by
          exact (Finset.sum_subtype
            ((Finset.univ :
              Finset (Finset (ConcretePlaquette d N))).filter
                (fun c' => c'.Nonempty ∧ IsConnectedPolymer c'))
            (fun c' => by simp)
            (fun c' => ((Real.exp (|β| * B) - 1) * Real.exp t) ^ c'.card)).symm
      _ ≤ ∑ c' ∈ (Finset.univ :
            Finset (Finset (ConcretePlaquette d N))).erase ∅,
            ((Real.exp (|β| * B) - 1) * Real.exp t) ^ c'.card := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun c' _ _ => by positivity)
          intro c' hc'
          rw [Finset.mem_filter] at hc'
          rw [Finset.mem_erase]
          exact ⟨Finset.nonempty_iff_ne_empty.mp hc'.2.1, Finset.mem_univ _⟩
      _ ≤ ((Real.exp (|β| * B) - 1) * Real.exp t + 1)
            ^ Fintype.card (ConcretePlaquette d N) - 1 := by
          have hsum := Finset.add_sum_erase
            (Finset.univ : Finset (Finset (ConcretePlaquette d N)))
            (fun c' => ((Real.exp (|β| * B) - 1) * Real.exp t) ^ c'.card)
            (Finset.mem_univ ∅)
          have hbin : ∑ c' ∈ (Finset.univ :
              Finset (Finset (ConcretePlaquette d N))),
              ((Real.exp (|β| * B) - 1) * Real.exp t) ^ c'.card
              = ((Real.exp (|β| * B) - 1) * Real.exp t + 1)
                ^ Fintype.card (ConcretePlaquette d N) := by
            rw [← Finset.powerset_univ]
            exact sum_powerset_pow_card _
          rw [← hbin]
          have hthis := hsum
          simp only [Finset.card_empty, pow_zero] at hthis
          linarith
      _ ≤ t := hsmall
      _ ≤ t * (c.1.card : ℝ) := by
          have hc1 : (1 : ℝ) ≤ (c.1.card : ℝ) := by
            exact_mod_cast c.2.1.card_pos
          nlinarith

/-- **Convergence of the connected-gas Mayer series** at small coupling. -/
theorem connectedLatticeClusterSum_summable
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) (t : ℝ) (ht0 : 0 ≤ t)
    (hsmall : ((Real.exp (|β| * B) - 1) * Real.exp t + 1)
        ^ Fintype.card (ConcretePlaquette d N) - 1 ≤ t)
    (hr : Real.exp 1 *
      (t * (Fintype.card (ConcretePlaquette d N) : ℝ)) < 1) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) →
        (connectedLatticePolymerSystem (d := d) (N := N) μ pe β).Polymer,
        (ursell (connectedLatticePolymerSystem (d := d) (N := N) μ pe β) X : ℂ) *
          ∏ i, (connectedLatticePolymerSystem (d := d) (N := N)
            μ pe β).activity (X i)) := by
  refine kp_convergence (connectedLatticePolymerSystem (d := d) (N := N) μ pe β)
    (connectedLatticePolymerSystem_kpCriterion_scaled (d := d) (N := N)
      μ hpe β t ht0 hsmall)
    (A := t * (Fintype.card (ConcretePlaquette d N) : ℝ))
    (by positivity) ?_ hr
  intro c
  have hcard : (c.1.card : ℝ) ≤ (Fintype.card (ConcretePlaquette d N) : ℝ) := by
    exact_mod_cast Finset.card_le_univ c.1
  exact mul_le_mul_of_nonneg_left hcard ht0

end YangMills
