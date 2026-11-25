/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.WilsonLine

/-!
# Holonomy gauge-covariance along a path (gauge-RG campaign, brick B4-prep)

`docs/BALABAN-RG-PLAN.md` B4.  The renormalization-group averaging
operator `Ū` (CMP 109 (0.12)) is gauge covariant because the contour
holonomies it averages transform by conjugation at their endpoints.
This file proves that endpoint law for an arbitrary connected path —
the foundation of B4 (gauge covariance) — using only the existing core
`wilsonLine`/`gaugeAct` machinery (no matrix logarithm needed).

**Source.** The contour/holonomy gauge law is standard; it is the law
underlying T. Bałaban, CMP 98 (1985) eq (11) and CMP 109 (1987) §0.
Strategy/framing: Lluis Eriksson (AIRR ARR-2026-4P13YY8RKA84FRBQ).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

/-- The endpoint of a path of edges starting at vertex `a`
(Bałaban's contour endpoint `x` / `c₊`). -/
def pathEnd (a : FinBox d N) :
    List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)) → FinBox d N
  | [] => a
  | e :: es => pathEnd (FiniteLatticeGeometry.dst e) es

/-- A list of edges is a **connected path from `a`**: each edge starts
where the previous one ended (the contour structure of CMP 95 (1.7)). -/
def IsPathFrom (a : FinBox d N) :
    List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)) → Prop
  | [] => True
  | e :: es => FiniteLatticeGeometry.src e = a
      ∧ IsPathFrom (FiniteLatticeGeometry.dst e) es

@[simp] theorem pathEnd_nil (a : FinBox d N) :
    pathEnd a ([] : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G))) = a :=
  rfl

@[simp] theorem pathEnd_cons (a : FinBox d N)
    (e : FiniteLatticeGeometry.E (d := d) (N := N) (G := G)) (es) :
    pathEnd a (e :: es) = pathEnd (FiniteLatticeGeometry.dst e) es :=
  rfl

/-- **Holonomy gauge-covariance law** (the B4 foundation): along a
connected path from `a` to its endpoint, the gauge-transformed Wilson
line conjugates by the gauge function at the two endpoints,
`wilsonLine (gaugeAct u A) es = u(a) · wilsonLine A es · u(end)⁻¹`. -/
theorem wilsonLine_gaugeAct_path (u : GaugeTransform d N G) (A : GaugeConfig d N G) :
    ∀ (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)))
      (a : FinBox d N), IsPathFrom a es →
      wilsonLine (gaugeAct u A) es
        = u a * wilsonLine A es * (u (pathEnd a es))⁻¹ := by
  intro es
  induction es with
  | nil =>
    intro a _
    simp only [wilsonLine_nil, pathEnd_nil]
    group
  | cons e es ih =>
    intro a hpath
    obtain ⟨hsrc, hrest⟩ := hpath
    simp only [wilsonLine_cons, gaugeAct_apply, pathEnd_cons]
    rw [ih (FiniteLatticeGeometry.dst e) hrest, ← hsrc]
    group

end YangMills.RG
