import YangMills.L0_Lattice.FiniteLattice

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace YangMills

/-- Cyclic successor on `Fin 4`. -/
def succ4 (i : Fin 4) : Fin 4 :=
  ⟨(i.1 + 1) % 4, by decide⟩

/--
Geometric structure required for finite-volume lattice gauge theory.

This packages the exact finite combinatorial data needed to talk about:
- edge reversal,
- source/target maps,
- ordered plaquette boundaries,
- and the closed-loop cancellation identity for gauge transformations.
-/
class FiniteLatticeGeometry (d N : ℕ) (G : Type _) [Group G] where
  src : OrientedEdge d N → FinBox d N
  dst : OrientedEdge d N → FinBox d N
  reverse : OrientedEdge d N → OrientedEdge d N

  reverse_involutive : ∀ e, reverse (reverse e) = e
  src_reverse : ∀ e, src (reverse e) = dst e
  dst_reverse : ∀ e, dst (reverse e) = src e

  plaquetteVertex : Plaquette d N → Fin 4 → FinBox d N
  plaquetteEdge : Plaquette d N → Fin 4 → OrientedEdge d N

  plaquetteEdge_src :
    ∀ p i, src (plaquetteEdge p i) = plaquetteVertex p i
  plaquetteEdge_dst :
    ∀ p i, dst (plaquetteEdge p i) = plaquetteVertex p (succ4 i)

  /--
  Telescoping cancellation identity for the ordered boundary of a plaquette.

  This is the exact closed-loop identity needed in the proof that plaquette holonomy
  transforms by conjugation under a gauge transformation.
  -/
  plaquette_gauge_telescope :
    ∀ (u : FinBox d N → G) (p : Plaquette d N),
      (u (plaquetteVertex p 0))⁻¹ *
          (u (plaquetteVertex p 0) * (u (plaquetteVertex p 1))⁻¹) *
          (u (plaquetteVertex p 1) * (u (plaquetteVertex p 2))⁻¹) *
          (u (plaquetteVertex p 2) * (u (plaquetteVertex p 3))⁻¹) *
          (u (plaquetteVertex p 3) * (u (plaquetteVertex p 0))⁻¹) *
          u (plaquetteVertex p 0)
        = 1

/-- A gauge transformation is a vertex-valued function. -/
abbrev GaugeTransform (d N : ℕ) (G : Type _) := FinBox d N → G

/--
A finite-volume gauge configuration assigns a group element to each oriented edge,
with reversal mapped to inversion.
-/
structure GaugeConfig (d N : ℕ) (G : Type _) [Group G]
    [FiniteLatticeGeometry d N G] where
  toFun : OrientedEdge d N → G
  map_reverse' :
    ∀ e, toFun (FiniteLatticeGeometry.reverse e) = (toFun e)⁻¹

namespace GaugeConfig

variable {d N : ℕ} {G : Type _}
variable [Group G] [FiniteLatticeGeometry d N G]

instance : CoeFun (GaugeConfig d N G) (fun _ => OrientedEdge d N → G) :=
  ⟨GaugeConfig.toFun⟩

@[simp]
theorem map_reverse (A : GaugeConfig d N G) (e : OrientedEdge d N) :
    A (FiniteLatticeGeometry.reverse e) = (A e)⁻¹ :=
  A.map_reverse' e

/--
Gauge action on configurations:
`(u • A)(e) = u(src e) * A(e) * u(dst e)⁻¹`.
-/
def gaugeAct (u : GaugeTransform d N G) (A : GaugeConfig d N G) :
    GaugeConfig d N G where
  toFun e :=
    u (FiniteLatticeGeometry.src e) * A e * (u (FiniteLatticeGeometry.dst e))⁻¹
  map_reverse' e := by
    rw [FiniteLatticeGeometry.src_reverse, FiniteLatticeGeometry.dst_reverse]
    rw [A.map_reverse]
    calc
      u (FiniteLatticeGeometry.dst e) * (A e)⁻¹ * (u (FiniteLatticeGeometry.src e))⁻¹
          =
        (u (FiniteLatticeGeometry.src e) * A e * (u (FiniteLatticeGeometry.dst e))⁻¹)⁻¹ := by
            group

@[simp]
theorem gaugeAct_apply (u : GaugeTransform d N G) (A : GaugeConfig d N G)
    (e : OrientedEdge d N) :
    gaugeAct u A e =
      u (FiniteLatticeGeometry.src e) * A e * (u (FiniteLatticeGeometry.dst e))⁻¹ :=
  rfl

end GaugeConfig
end YangMills
