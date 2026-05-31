/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations

/-!
# Wilson lines as ordered edge products, and their centre scaling (LG6)

A **Wilson line** along an ordered list of edges is the ordered product of the edge
holonomies, `(edges.map A).prod`.  Because the gauge group is **non-commutative**, the
product must be an *ordered* `List.prod`, not a `Finset.prod` (which needs `CommMonoid`).

This file packages the Wilson line as a named observable `wilsonLine` over an arbitrary
edge list, and proves its **centre scaling law**: under the diagonal centre action
`A ↦ (e ↦ z·A e)` with central `z`, a length-`L` Wilson line scales by `z^L`.

This generalizes `WilsonLoopCenter.plaquetteHolonomy_center_smul` (the `L = 4` plaquette)
to arbitrary length, and is the algebraic core of the Wilson-loop selection rule: a closed
loop of length `L` is a centre eigenfunction with eigenvalue `z^L`, so its expectation is
forced to zero exactly when a central character has `z^L ≠ 1` (`N ∤ L` for the `Z_N` centre
of SU(N)) — and is *not* forced to zero otherwise (the area-law contributor).  The
remaining measure-theoretic step (centre-invariance of `gaugeMeasureFrom`) is `HORIZON.md`
LG6.

Oracle target: `[propext, Quot.sound]` (pure algebra). No sorry, no axioms.
-/

namespace YangMills.GaugeConfig

open YangMills

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

/-- The **Wilson line** along an ordered edge list `es`: the ordered product of the edge
holonomies `(es.map A).prod`.  (For a closed loop, `es` returns to its start; the trace of
this element is the Wilson-loop observable.) -/
def wilsonLine (A : GaugeConfig d N G)
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G))) : G :=
  (es.map (fun e => A e)).prod

@[simp] theorem wilsonLine_nil (A : GaugeConfig d N G) :
    wilsonLine A ([] : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G))) = 1 := by
  simp [wilsonLine]

/-- **Centre scaling of an ordered list product.**  If `z` is central, scaling each factor
of an ordered list product by `z` multiplies the product by `z^(length)`. -/
theorem center_listProd_scaling {z : G} (hz : ∀ y : G, Commute z y) (l : List G) :
    (l.map (fun g => z * g)).prod = z ^ l.length * l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.prod_cons, ih, List.length_cons, List.prod_cons, pow_succ']
    -- Goal: z * a * (z^n * t.prod) = z * z^n * (a * t.prod); commute a with z^n (z central).
    have hcomm : a * (z ^ t.length * t.prod) = z ^ t.length * (a * t.prod) := by
      rw [← mul_assoc, ((hz a).symm.pow_right _).eq, mul_assoc]
    rw [mul_assoc z a, hcomm, ← mul_assoc]

/-- **Wilson line centre scaling law.**  Under the diagonal centre rescaling of every edge
by a central `z` (`Az e = z · A e`), a Wilson line along an edge list `es` of length `L` is
multiplied by `z^L`.  This is the centre eigenvalue identity for an arbitrary-length
line/loop (the `L = 4` plaquette case is `WilsonLoopCenter.plaquetteHolonomy_center_smul`). -/
theorem wilsonLine_center_smul {z : G} (hz : ∀ y : G, Commute z y)
    (A Az : GaugeConfig d N G)
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)))
    (hAz : ∀ e, Az e = z * A e) :
    wilsonLine Az es = z ^ es.length * wilsonLine A es := by
  unfold wilsonLine
  have hmap : (es.map (fun e => Az e)) = (es.map (fun e => A e)).map (fun g => z * g) := by
    rw [List.map_map]
    exact List.map_congr_left (fun e _ => by rw [Function.comp_apply, hAz e])
  rw [hmap, center_listProd_scaling hz, List.length_map]

end YangMills.GaugeConfig
