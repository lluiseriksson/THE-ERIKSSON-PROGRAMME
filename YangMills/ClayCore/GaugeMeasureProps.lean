/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.GaugeMarginal

/-!
# General properties of the lattice gauge measure

A block of reusable facts about `gaugeMeasureFrom μ` and single-edge observables: the
total mass, the expectation of constants, linearity consequences, and the conjugate/real
forms of the single-edge reduction.  These are the routine measure-theoretic lemmas that
the Wilson-correlator estimates rest on; all are oracle-clean.
-/

namespace YangMills

open MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-- The gauge measure is a probability measure (total mass `1`). -/
theorem gaugeMeasureFrom_univ (μ : Measure G) [IsProbabilityMeasure μ] :
    (gaugeMeasureFrom (d := d) (N := N) μ) Set.univ = 1 :=
  measure_univ

/-- The expectation of a constant observable is the constant. -/
theorem gauge_integral_const (μ : Measure G) [IsProbabilityMeasure μ] (c : ℂ) :
    ∫ _A : GaugeConfig d N G, c ∂(gaugeMeasureFrom (d := d) (N := N) μ) = c := by
  simp [integral_const]

/-- The expectation of the constant `1` observable is `1`. -/
theorem gauge_integral_one (μ : Measure G) [IsProbabilityMeasure μ] :
    ∫ _A : GaugeConfig d N G, (1 : ℂ) ∂(gaugeMeasureFrom (d := d) (N := N) μ) = 1 := by
  rw [gauge_integral_const]

/-- The single-edge reduction respects scalar multiples: `∫ c·f(A e) = c·∫ f dμ`. -/
theorem integral_single_edge_const_smul (μ : Measure G) [IsProbabilityMeasure μ]
    (e : PosEdge d N) (c : ℂ) (f : G → ℂ) (hf : AEStronglyMeasurable f μ) :
    ∫ A, c * f (configToPos A e) ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = c * ∫ g, f g ∂μ := by
  have h := integral_single_edge (d := d) (N := N) μ e (fun g => c * f g)
    (hf.const_mul c)
  simp only at h
  rw [h]; exact integral_const_mul c f

/-- The single-edge reduction respects the conjugate: `∫ conj(f(A e)) = conj(∫ f dμ)`. -/
theorem integral_single_edge_conj (μ : Measure G) [IsProbabilityMeasure μ]
    (e : PosEdge d N) (f : G → ℂ) (hf : AEStronglyMeasurable f μ) :
    ∫ A, (starRingEnd ℂ) (f (configToPos A e)) ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = (starRingEnd ℂ) (∫ g, f g ∂μ) := by
  have h := integral_single_edge (d := d) (N := N) μ e (fun g => (starRingEnd ℂ) (f g))
    (Complex.continuous_conj.comp_aestronglyMeasurable hf)
  simp only at h
  rw [h]; exact integral_conj

end YangMills
