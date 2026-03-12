import Mathlib
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L0_Lattice.GaugeInvariance
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

namespace YangMills

/-! # L1.1 / L1.2: Gibbs measure (PARTIAL — stubs) -/

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]
variable [MeasurableSpace G] [MeasurableSpace (GaugeConfig d N G)]

/-- Partition function (stub). -/
noncomputable def partitionFunction
    (plaquetteEnergy : G → ℝ) (β : ℝ) : ℝ := sorry

/-- Gibbs measure (stub). -/
noncomputable def gibbsMeasure
    (plaquetteEnergy : G → ℝ) (β : ℝ) :
    MeasureTheory.Measure (GaugeConfig d N G) := sorry

end YangMills
