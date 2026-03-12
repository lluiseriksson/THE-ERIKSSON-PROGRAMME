import Mathlib
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L0_Lattice.GaugeInvariance
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

namespace YangMills

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

/-! ## Measurable structure on GaugeConfig -/

@[ext]
theorem GaugeConfig.ext {A B : GaugeConfig d N G} (h : ∀ e, A e = B e) : A = B := by
  cases A; cases B; congr; funext e; exact h e

def GaugeConfig.equivSubtype :
    GaugeConfig d N G ≃
    {f : FiniteLatticeGeometry.E (d:=d) (N:=N) (G:=G) → G //
      ∀ e, f (FiniteLatticeGeometry.reverse e) = (f e)⁻¹} :=
  { toFun  := fun A => ⟨A.toFun, A.map_reverse⟩
    invFun := fun ⟨f, hf⟩ => ⟨f, hf⟩
    left_inv  := fun A => by ext e; rfl
    right_inv := fun ⟨f, _⟩ => rfl }

instance [MeasurableSpace G] : MeasurableSpace (GaugeConfig d N G) :=
  MeasurableSpace.comap GaugeConfig.equivSubtype.toFun inferInstance

/-! ## L1.1 / L1.2: Partition function and Gibbs measure -/

/-- Partition function (stub — Haar measure integration pending). -/
noncomputable def partitionFunction [MeasurableSpace G]
    (plaquetteEnergy : G → ℝ) (β : ℝ) : ℝ := sorry

/-- Gibbs measure (stub — Haar measure pending). -/
noncomputable def gibbsMeasure [MeasurableSpace G]
    (plaquetteEnergy : G → ℝ) (β : ℝ) :
    MeasureTheory.Measure (GaugeConfig d N G) := sorry

end YangMills
