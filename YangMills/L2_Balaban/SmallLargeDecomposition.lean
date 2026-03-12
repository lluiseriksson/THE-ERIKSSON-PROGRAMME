import Mathlib.MeasureTheory.Measure.Haar.Basic
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L1_GibbsMeasure.GibbsMeasure

namespace YangMills

variable {d N : ℕ} {G : Type _} [Group G] [FiniteLatticeGeometry d N G]
variable [TopologicalGroup G] [CompactSpace G] [MeasureSpace G]
  [IsHaarMeasure (haarMeasure (1 : G))]

/-!
# L2.1: Balaban small/large-field decomposition (abstract, safe draft)
No placeholders, no early SU(2), depends only on closed L1 interfaces.
-/

/-- Small-field cutoff parameter (dimensionless). -/
variable (κ : ℝ) [Fact (0 < κ)]

/-- Small-field region: configurations where Wilson action ≤ κ. -/
def SmallFieldSet : Set (GaugeConfig d N G) :=
  { U | wilsonAction U ≤ κ }

/-- Large-field complement. -/
def LargeFieldSet : Set (GaugeConfig d N G) := SmallFieldSetᶜ

/-- Characteristic functions for the decomposition. -/
noncomputable def χ_small : GaugeConfig d N G → ℝ :=
  Set.indicator SmallFieldSet 1

noncomputable def χ_large : GaugeConfig d N G → ℝ :=
  Set.indicator LargeFieldSet 1

theorem decomposition_identity :
    ∀ U, χ_small U + χ_large U = 1 := by
  intro U
  by_cases h : U ∈ SmallFieldSet
  · simp [χ_small, χ_large, h]
  · simp [χ_small, χ_large, h]

/-- Balaban decomposition of the Gibbs measure (abstract form). -/
noncomputable def balabanDecomposition (β : ℝ) : Measure (GaugeConfig d N G) :=
  (χ_small • gibbsMeasure β) + (χ_large • gibbsMeasure β)

theorem balabanDecomposition_isGibbs (β : ℝ) :
    balabanDecomposition β = gibbsMeasure β := by
  ext U
  simp [balabanDecomposition, decomposition_identity]
  ring

end YangMills
