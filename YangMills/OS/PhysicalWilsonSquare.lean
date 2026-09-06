import YangMills.L0_Lattice.GaugeConfigurations

/-!
# The four-link Wilson square and its geometric reflection

Four independently assigned positive links, ordered bottom/right/top/left.
The boundary orientation is bottom, right, reversed top, reversed left.
The dictionary below is an equality with the repository's plaquette holonomy.
Gauge covariance is already proved by `GaugeConfig.plaquetteHolonomy_gaugeAct`
in `L0_Lattice/WilsonAction.lean`; it is deliberately not reproved here.

This module proves local boundary geometry only. It does not define a global
lattice reflection, prove a product-Haar identity, reflection positivity,
reconstruct a Hilbert space, or establish a mass gap.
-/

namespace YangMills.OS

abbrev WilsonSquare (G : Type*) := Fin 4 → G

namespace WilsonSquare

variable {G : Type*} [Group G]

/-- The actual ordered Wilson boundary word. -/
def holonomy (A : WilsonSquare G) : G :=
  A 0 * A 1 * (A 2)⁻¹ * (A 3)⁻¹

/-- Reflection through the vertical bisector reverses both horizontal links
and exchanges the two vertical links. -/
def reflect (A : WilsonSquare G) : WilsonSquare G :=
  ![(A 0)⁻¹, A 3, (A 2)⁻¹, A 1]

theorem reflect_involutive : Function.Involutive (reflect (G := G)) := by
  intro A
  funext i
  fin_cases i <;> simp [reflect]

/-- The reflected boundary is the reversed original boundary, rebased at
the reflected lower-left vertex by the bottom transporter. -/
theorem holonomy_reflect (A : WilsonSquare G) :
    holonomy (reflect A) = (A 0)⁻¹ * (holonomy A)⁻¹ * A 0 := by
  change (A 0)⁻¹ * A 3 * ((A 2)⁻¹)⁻¹ * (A 1)⁻¹ =
    (A 0)⁻¹ * (A 0 * A 1 * (A 2)⁻¹ * (A 3)⁻¹)⁻¹ * A 0
  group

/-- The two half-boundary paths have distinct crossing transporters. -/
theorem holonomy_eq_relative_paths (A : WilsonSquare G) :
    holonomy A = (A 0 * A 1) * (A 3 * A 2)⁻¹ := by
  unfold holonomy
  group

section Dictionary

variable {d N : ℕ} [FiniteLatticeGeometry d N G]

/-- Extract the four positive boundary variables from a genuine configuration.
The third and fourth stored boundary edges are traversed in reverse, so their
values are inverted to obtain the positive-link coordinates. -/
def ofPlaquette (A : GaugeConfig d N G)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) : WilsonSquare G :=
  ![A (FiniteLatticeGeometry.plaquetteEdge p 0),
    A (FiniteLatticeGeometry.plaquetteEdge p 1),
    (A (FiniteLatticeGeometry.plaquetteEdge p 2))⁻¹,
    (A (FiniteLatticeGeometry.plaquetteEdge p 3))⁻¹]

/-- Source dictionary: this boundary word is the existing physical holonomy,
not an equality supplied by the caller. -/
theorem holonomy_ofPlaquette (A : GaugeConfig d N G)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) :
    holonomy (ofPlaquette A p) = GaugeConfig.plaquetteHolonomy A p := by
  simp [holonomy, ofPlaquette, GaugeConfig.plaquetteHolonomy]

end Dictionary

/-- Every fixed choice of the other links leaves an injective dependence on
the bottom crossing link. -/
theorem bottom_injective (r t l : G) :
    Function.Injective (fun b : G => holonomy ![b, r, t, l]) := by
  intro a b h
  change a * r * t⁻¹ * l⁻¹ = b * r * t⁻¹ * l⁻¹ at h
  exact mul_right_cancel (mul_right_cancel (mul_right_cancel h))

theorem right_injective (b t l : G) :
    Function.Injective (fun r : G => holonomy ![b, r, t, l]) := by
  intro a c h
  change b * a * t⁻¹ * l⁻¹ = b * c * t⁻¹ * l⁻¹ at h
  exact mul_left_cancel (mul_right_cancel (mul_right_cancel h))

/-- The second crossing link has its own injective dependence; it has not
been identified with the first and cancelled. -/
theorem top_injective (b r l : G) :
    Function.Injective (fun t : G => holonomy ![b, r, t, l]) := by
  intro a c h
  change b * r * a⁻¹ * l⁻¹ = b * r * c⁻¹ * l⁻¹ at h
  exact inv_injective (mul_left_cancel (mul_right_cancel h))

theorem left_injective (b r t : G) :
    Function.Injective (fun l : G => holonomy ![b, r, t, l]) := by
  intro a c h
  change b * r * t⁻¹ * a⁻¹ = b * r * t⁻¹ * c⁻¹ at h
  exact inv_injective (mul_left_cancel h)

/-- A direct nonidentity boundary witness, valid in particular for SU(2).
This is not a nonzero OS fluctuation-sector witness. -/
theorem holonomy_single_bottom_ne_one (u : G) (hu : u ≠ 1) :
    holonomy ![u, 1, 1, 1] ≠ 1 := by
  simpa [holonomy] using hu

end WilsonSquare

end YangMills.OS
