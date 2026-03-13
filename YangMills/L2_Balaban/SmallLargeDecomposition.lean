import Mathlib
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L1_GibbsMeasure.GibbsMeasure

namespace YangMills

open MeasureTheory Set

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]
variable (κ : ℝ) (plaquetteEnergy : G → ℝ)

/-! ## L2.1: Bałaban small/large-field decomposition -/

/-- Small-field region: configurations where Wilson action ≤ κ. -/
def SmallFieldSet : Set (GaugeConfig d N G) :=
  {U | wilsonAction plaquetteEnergy U ≤ κ}

/-- Large-field complement. -/
def LargeFieldSet : Set (GaugeConfig d N G) :=
  {U | κ < wilsonAction plaquetteEnergy U}

omit [MeasurableSpace G] in
theorem smallLarge_partition :
    SmallFieldSet (d:=d) (N:=N) κ plaquetteEnergy ∪
    LargeFieldSet (d:=d) (N:=N) κ plaquetteEnergy = Set.univ := by
  ext U; simp [SmallFieldSet, LargeFieldSet, le_or_gt]

omit [MeasurableSpace G] in
theorem smallLarge_disjoint :
    Disjoint (SmallFieldSet (d:=d) (N:=N) κ plaquetteEnergy)
             (LargeFieldSet (d:=d) (N:=N) κ plaquetteEnergy) := by
  simp [Set.disjoint_left, SmallFieldSet, LargeFieldSet, not_lt]

/-- Characteristic function of the small-field region. -/
noncomputable def χ_small : GaugeConfig d N G → ℝ :=
  (SmallFieldSet κ plaquetteEnergy).indicator (fun _ => 1)

/-- Characteristic function of the large-field region. -/
noncomputable def χ_large : GaugeConfig d N G → ℝ :=
  (LargeFieldSet κ plaquetteEnergy).indicator (fun _ => 1)

omit [MeasurableSpace G] in
theorem decomposition_identity (U : GaugeConfig d N G) :
    χ_small κ plaquetteEnergy U + χ_large κ plaquetteEnergy U = 1 := by
  simp only [χ_small, χ_large, SmallFieldSet, LargeFieldSet,
             Set.indicator, Set.mem_setOf_eq]
  by_cases h : wilsonAction plaquetteEnergy U ≤ κ <;> simp [h, not_lt.mpr]

end YangMills
