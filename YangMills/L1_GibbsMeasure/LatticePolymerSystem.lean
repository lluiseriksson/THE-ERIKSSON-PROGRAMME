/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Basic
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

end YangMills
