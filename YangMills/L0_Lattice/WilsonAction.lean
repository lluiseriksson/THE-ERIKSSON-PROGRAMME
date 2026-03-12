import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations

open scoped BigOperators

namespace YangMills

namespace GaugeConfig

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

theorem plaquetteHolonomy_gaugeAct
    (u : GaugeTransform d N G) (A : GaugeConfig d N G)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) :
    plaquetteHolonomy (gaugeAct u A) p =
      u (FiniteLatticeGeometry.plaquetteVertex p 0) *
        plaquetteHolonomy A p *
        (u (FiniteLatticeGeometry.plaquetteVertex p 0))⁻¹ := by
  simp only [plaquetteHolonomy, gaugeAct_apply,
             FiniteLatticeGeometry.plaquetteEdge_src,
             FiniteLatticeGeometry.plaquetteEdge_dst]
  -- succ4 0 = 1, succ4 1 = 2, succ4 2 = 3, succ4 3 = 0
  have h0 : succ4 0 = 1 := by decide
  have h1 : succ4 1 = 2 := by decide
  have h2 : succ4 2 = 3 := by decide
  have h3 : succ4 3 = 0 := by decide
  rw [h0, h1, h2, h3]
  group

end GaugeConfig

section WilsonAction

variable {d N : ℕ} {G : Type*} [Group G] [inst : FiniteLatticeGeometry d N G]

def ConjInvariant (plaquetteEnergy : G → ℝ) : Prop :=
  ∀ g x, plaquetteEnergy (g * x * g⁻¹) = plaquetteEnergy x

noncomputable def wilsonAction (plaquetteEnergy : G → ℝ) (A : GaugeConfig d N G) : ℝ :=
  haveI : Fintype (FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) := inst.fintypeP
  ∑ p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G),
    plaquetteEnergy (GaugeConfig.plaquetteHolonomy A p)

end WilsonAction
end YangMills
