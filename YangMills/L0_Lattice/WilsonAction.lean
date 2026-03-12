import YangMills.L0_Lattice.GaugeConfigurations

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace YangMills

namespace GaugeConfig

variable {d N : ℕ} {G : Type _}
variable [Group G] [FiniteLatticeGeometry d N G]

/-- Ordered plaquette holonomy. -/
def plaquetteHolonomy (A : GaugeConfig d N G) (p : Plaquette d N) : G :=
  A (FiniteLatticeGeometry.plaquetteEdge p 0) *
    A (FiniteLatticeGeometry.plaquetteEdge p 1) *
    A (FiniteLatticeGeometry.plaquetteEdge p 2) *
    A (FiniteLatticeGeometry.plaquetteEdge p 3)

@[simp]
theorem plaquetteHolonomy_def (A : GaugeConfig d N G) (p : Plaquette d N) :
    plaquetteHolonomy A p =
      A (FiniteLatticeGeometry.plaquetteEdge p 0) *
        A (FiniteLatticeGeometry.plaquetteEdge p 1) *
        A (FiniteLatticeGeometry.plaquetteEdge p 2) *
        A (FiniteLatticeGeometry.plaquetteEdge p 3) :=
  rfl

/--
Under a gauge transformation, plaquette holonomy transforms by conjugation
with the gauge value at the base vertex.
-/
theorem plaquetteHolonomy_gaugeAct
    (u : GaugeTransform d N G) (A : GaugeConfig d N G) (p : Plaquette d N) :
    plaquetteHolonomy (gaugeAct u A) p =
      u (FiniteLatticeGeometry.plaquetteVertex p 0) *
        plaquetteHolonomy A p *
        (u (FiniteLatticeGeometry.plaquetteVertex p 0))⁻¹ := by
  -- Expand the definition.
  simp [plaquetteHolonomy, GaugeConfig.gaugeAct,
    FiniteLatticeGeometry.plaquetteEdge_src,
    FiniteLatticeGeometry.plaquetteEdge_dst,
    mul_assoc]

  -- We want to collapse the intermediate gauge factors along the closed plaquette loop.
  -- The needed identity is provided by the geometry interface.
  let v0 := u (FiniteLatticeGeometry.plaquetteVertex p 0)
  let v1 := u (FiniteLatticeGeometry.plaquetteVertex p 1)
  let v2 := u (FiniteLatticeGeometry.plaquetteVertex p 2)
  let v3 := u (FiniteLatticeGeometry.plaquetteVertex p 3)

  have htelescope :=
    FiniteLatticeGeometry.plaquette_gauge_telescope (d := d) (N := N) (G := G) u p

  -- Reduce to a pure group identity using the telescoping axiom.
  dsimp [v0, v1, v2, v3] at htelescope ⊢
  group_apply at htelescope ⊢
  -- wait, 'group' tactic might not work on un-reduced terms in hypothesis, 
  -- actually the original code had 'group at htelescope ⊢' which is correct if it works.
  -- Let's just use the original content:
  group at htelescope ⊢
  simpa using htelescope

end GaugeConfig

section WilsonAction

variable {d N : ℕ} {G : Type _}
variable [Group G] [FiniteLatticeGeometry d N G]

/-- Conjugation-invariant plaquette energy. -/
def ConjInvariant (plaquetteEnergy : G → ℝ) : Prop :=
  ∀ g x, plaquetteEnergy (g * x * g⁻¹) = plaquetteEnergy x

/-- Wilson-type finite-volume action. -/
def wilsonAction (plaquetteEnergy : G → ℝ) (A : GaugeConfig d N G) : ℝ :=
  ∑ p : Plaquette d N, plaquetteEnergy (GaugeConfig.plaquetteHolonomy A p)

end WilsonAction
end YangMills
