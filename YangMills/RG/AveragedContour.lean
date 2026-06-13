/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.RG.GroupAverage
import YangMills.RG.HolonomyGauge

/-!
# Gauge covariance of the averaged contour variable (gauge-RG campaign, brick B4)

`docs/BALABAN-RG-PLAN.md` B4.  Bałaban's averaged contour variable
(CMP 109 (0.11)) `U(y,x) = M({U(Γ)}_{Γ ∈ G(y,x)})` is the group average
of the holonomies along all contours from `y` to `x`.  Because every
such holonomy conjugates by the gauge functions at the SAME endpoints
`y, x` (the holonomy gauge law, brick B4-prep), and the group average
`M` is bi-equivariant (CMP 109 (0.6)), the averaged variable is gauge
covariant:

  `U(y,x)[gaugeAct u A] = u(y) · U(y,x)[A] · u(x)⁻¹`.

This is the gauge covariance (CMP 98 (11)) at the level of the averaged
variable — the step that makes the renormalization-group field map `Ū`
gauge covariant.  It needs **no matrix logarithm**: it is purely the
holonomy law `wilsonLine_gaugeAct_path` composed with
`GroupAverage.biequiv`.

**Source.** T. Bałaban, CMP 109 (1987) (0.6), (0.11); CMP 98 (1985)
(11).  Strategy/framing: Lluis Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

/-- **Gauge covariance of the averaged contour variable** (CMP 109
(0.11)): for any group average `Avg`, gauge transform `u`, configuration
`A`, and a nonempty family `paths` of connected contours all running
from `y` to `x`, the `Avg`-averaged holonomy conjugates by `u` at the
endpoints.  Combines the holonomy gauge law (B4-prep) with the
bi-equivariance (0.6) of the average. -/
theorem averagedContour_gaugeAct (Avg : GroupAverage G)
    (u : GaugeTransform d N G) (A : GaugeConfig d N G) (y x : FinBox d N)
    (paths : Multiset
      (List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G))))
    (hne : paths ≠ 0)
    (hpaths : ∀ Γ ∈ paths, IsPathFrom y Γ ∧ pathEnd y Γ = x) :
    Avg.M (paths.map (fun Γ => wilsonLine (gaugeAct u A) Γ))
      = u y * Avg.M (paths.map (fun Γ => wilsonLine A Γ)) * (u x)⁻¹ := by
  have hmap : paths.map (fun Γ => wilsonLine (gaugeAct u A) Γ)
      = (paths.map (fun Γ => wilsonLine A Γ)).map
          (fun W => u y * W * (u x)⁻¹) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun Γ hΓ => ?_
    obtain ⟨hpath, hend⟩ := hpaths Γ hΓ
    simp only [Function.comp_apply]
    rw [wilsonLine_gaugeAct_path u A Γ y hpath, hend]
  rw [hmap]
  exact Avg.biequiv (u y) (u x)⁻¹ _
    (fun h => hne (Multiset.map_eq_zero.mp h))

end YangMills.RG
