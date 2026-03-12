import Mathlib
import YangMills.L0_Lattice.FiniteLattice

namespace YangMills

/-- Cyclic successor on Fin 4. -/
def succ4 (i : Fin 4) : Fin 4 := ⟨(i.1 + 1) % 4, by omega⟩

/--
Abstract geometric structure for finite-volume lattice gauge theory.
Parametrized by edge type E and plaquette type P.
-/
class FiniteLatticeGeometry (d N : ℕ) (G : Type*) [Group G] where
  E : Type*
  P : Type*
  [fintypeE : Fintype E]
  [fintypeP : Fintype P]
  src      : E → FinBox d N
  dst      : E → FinBox d N
  reverse  : E → E
  reverse_involutive : ∀ e : E, reverse (reverse e) = e
  src_reverse : ∀ e : E, src (reverse e) = dst e
  dst_reverse : ∀ e : E, dst (reverse e) = src e
  plaquetteVertex : P → Fin 4 → FinBox d N
  plaquetteEdge   : P → Fin 4 → E
  plaquetteEdge_src : ∀ p i, src (plaquetteEdge p i) = plaquetteVertex p i
  plaquetteEdge_dst : ∀ p i, dst (plaquetteEdge p i) = plaquetteVertex p (succ4 i)
  plaquette_gauge_telescope :
    ∀ (u : FinBox d N → G) (p : P),
      (u (plaquetteVertex p 0))⁻¹ *
        (u (plaquetteVertex p 0) * (u (plaquetteVertex p 1))⁻¹) *
        (u (plaquetteVertex p 1) * (u (plaquetteVertex p 2))⁻¹) *
        (u (plaquetteVertex p 2) * (u (plaquetteVertex p 3))⁻¹) *
        (u (plaquetteVertex p 3) * (u (plaquetteVertex p 0))⁻¹) *
        u (plaquetteVertex p 0) = 1

attribute [reducible] FiniteLatticeGeometry.fintypeE
attribute [reducible] FiniteLatticeGeometry.fintypeP

/-- A gauge transformation is a vertex-valued function. -/
abbrev GaugeTransform (d N : ℕ) (G : Type*) := FinBox d N → G

/-- A finite-volume gauge configuration assigns a group element to each edge,
    with reversal mapped to inversion. -/
structure GaugeConfig (d N : ℕ) (G : Type*) [Group G]
    [FiniteLatticeGeometry d N G] where
  toFun      : (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)) → G
  map_reverse : ∀ e, toFun (FiniteLatticeGeometry.reverse e) = (toFun e)⁻¹

namespace GaugeConfig

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

instance : CoeFun (GaugeConfig d N G)
    (fun _ => FiniteLatticeGeometry.E (d := d) (N := N) (G := G) → G) :=
  ⟨GaugeConfig.toFun⟩

/-- Plaquette holonomy: ordered product around a plaquette boundary. -/
def plaquetteHolonomy (A : GaugeConfig d N G)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) : G :=
  A (FiniteLatticeGeometry.plaquetteEdge p 0) *
  A (FiniteLatticeGeometry.plaquetteEdge p 1) *
  A (FiniteLatticeGeometry.plaquetteEdge p 2) *
  A (FiniteLatticeGeometry.plaquetteEdge p 3)

/-- Gauge action: (u • A)(e) = u(src e) · A(e) · u(dst e)⁻¹ -/
def gaugeAct (u : GaugeTransform d N G) (A : GaugeConfig d N G) :
    GaugeConfig d N G where
  toFun e :=
    u (FiniteLatticeGeometry.src e) * A e * (u (FiniteLatticeGeometry.dst e))⁻¹
  map_reverse e := by
    simp only [FiniteLatticeGeometry.src_reverse, FiniteLatticeGeometry.dst_reverse,
               GaugeConfig.map_reverse]
    group

@[simp]
theorem gaugeAct_apply (u : GaugeTransform d N G) (A : GaugeConfig d N G) (e) :
    gaugeAct u A e =
      u (FiniteLatticeGeometry.src e) * A e * (u (FiniteLatticeGeometry.dst e))⁻¹ :=
  rfl

end GaugeConfig
end YangMills
