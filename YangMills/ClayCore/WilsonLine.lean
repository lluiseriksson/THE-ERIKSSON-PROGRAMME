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

@[simp] theorem wilsonLine_singleton (A : GaugeConfig d N G)
    (e : FiniteLatticeGeometry.E (d := d) (N := N) (G := G)) :
    wilsonLine A [e] = A e := by
  simp [wilsonLine]

theorem wilsonLine_cons (A : GaugeConfig d N G)
    (e : FiniteLatticeGeometry.E (d := d) (N := N) (G := G))
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G))) :
    wilsonLine A (e :: es) = A e * wilsonLine A es := by
  simp [wilsonLine, List.map_cons, List.prod_cons]

/-- **Composition of Wilson lines.**  The Wilson line of a concatenated path is the ordered
product of the Wilson lines of the pieces: `wilsonLine A (es₁ ++ es₂) = wilsonLine A es₁ *
wilsonLine A es₂`.  This is the composition law that lets a closed loop be split into
sub-paths (and underlies the multiplicativity of holonomies along a contour). -/
theorem wilsonLine_append (A : GaugeConfig d N G)
    (es₁ es₂ : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G))) :
    wilsonLine A (es₁ ++ es₂) = wilsonLine A es₁ * wilsonLine A es₂ := by
  simp [wilsonLine, List.map_append, List.prod_append]

/-- **The plaquette holonomy is the Wilson line of its four boundary edges.**  Connects the
existing `plaquetteHolonomy` (`L0_Lattice`) to the general `wilsonLine`: the plaquette is
the closed length-4 Wilson loop. -/
theorem plaquetteHolonomy_eq_wilsonLine (A : GaugeConfig d N G)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) :
    plaquetteHolonomy A p
      = wilsonLine A [FiniteLatticeGeometry.plaquetteEdge p 0,
          FiniteLatticeGeometry.plaquetteEdge p 1,
          FiniteLatticeGeometry.plaquetteEdge p 2,
          FiniteLatticeGeometry.plaquetteEdge p 3] := by
  simp only [plaquetteHolonomy, wilsonLine, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc]

/-- Two-edge Wilson line: `wilsonLine A [e₁, e₂] = A e₁ * A e₂`. -/
@[simp] theorem wilsonLine_pair (A : GaugeConfig d N G)
    (e₁ e₂ : FiniteLatticeGeometry.E (d := d) (N := N) (G := G)) :
    wilsonLine A [e₁, e₂] = A e₁ * A e₂ := by
  rw [wilsonLine_cons, wilsonLine_singleton]

/-- **Snoc law.**  Appending an edge on the right multiplies the line on the right:
`wilsonLine A (es ++ [e]) = wilsonLine A es * A e`. -/
theorem wilsonLine_append_singleton (A : GaugeConfig d N G)
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)))
    (e : FiniteLatticeGeometry.E (d := d) (N := N) (G := G)) :
    wilsonLine A (es ++ [e]) = wilsonLine A es * A e := by
  rw [wilsonLine_append, wilsonLine_singleton]

/-- The Wilson line of the **trivial (identity) configuration** is `1` for any path. -/
theorem wilsonLine_one
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)))
    (A : GaugeConfig d N G) (hA : ∀ e, A e = 1) :
    wilsonLine A es = 1 := by
  unfold wilsonLine
  rw [show (es.map (fun e => A e)) = es.map (fun _ => (1 : G)) from
    List.map_congr_left (fun e _ => hA e)]
  simp

/-- **Length additivity under concatenation** (a sanity invariant of the path length used
by the centre exponent `z^L`): the centre exponent of a concatenated path is the sum. -/
theorem wilsonLine_append_length
    (es₁ es₂ : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G))) :
    (es₁ ++ es₂).length = es₁.length + es₂.length :=
  List.length_append

/-- The Wilson line of a **flattened** list of paths is the ordered product of the pieces'
Wilson lines. -/
theorem wilsonLine_flatten (A : GaugeConfig d N G)
    (P : List (List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)))) :
    wilsonLine A P.flatten = (P.map (fun es => wilsonLine A es)).prod := by
  induction P with
  | nil => simp
  | cons es rest ih =>
    rw [List.flatten_cons, wilsonLine_append, ih, List.map_cons, List.prod_cons]

/-- **Gauge action is multiplicative on edges.**  `gaugeAct u A e = u(src e) · A e · u(dst e)⁻¹`
restated as the defining identity (a convenient rewrite). -/
theorem wilsonLine_gaugeAct_cons (u : GaugeTransform d N G) (A : GaugeConfig d N G)
    (e : FiniteLatticeGeometry.E (d := d) (N := N) (G := G))
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G))) :
    wilsonLine (gaugeAct u A) (e :: es)
      = (u (FiniteLatticeGeometry.src e) * A e * (u (FiniteLatticeGeometry.dst e))⁻¹)
        * wilsonLine (gaugeAct u A) es := by
  rw [wilsonLine_cons, gaugeAct_apply]

/-- **Trivial gauge transformation acts trivially on the Wilson line.**  If `u ≡ 1`, then
`gaugeAct u A` has the same Wilson line as `A` (gauge invariance at the identity). -/
theorem wilsonLine_gaugeAct_one (u : GaugeTransform d N G) (A : GaugeConfig d N G)
    (hu : ∀ v, u v = 1)
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G))) :
    wilsonLine (gaugeAct u A) es = wilsonLine A es := by
  have hpt : ∀ e, gaugeAct u A e = A e := by
    intro e; rw [gaugeAct_apply, hu, hu]; group
  unfold wilsonLine
  exact congrArg List.prod (List.map_congr_left (fun e _ => hpt e))

/-- The single-edge gauge-transformed line: `wilsonLine (gaugeAct u A) [e]
= u(src e)·A e·u(dst e)⁻¹`. -/
@[simp] theorem wilsonLine_gaugeAct_singleton (u : GaugeTransform d N G) (A : GaugeConfig d N G)
    (e : FiniteLatticeGeometry.E (d := d) (N := N) (G := G)) :
    wilsonLine (gaugeAct u A) [e]
      = u (FiniteLatticeGeometry.src e) * A e * (u (FiniteLatticeGeometry.dst e))⁻¹ := by
  rw [wilsonLine_singleton, gaugeAct_apply]

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

section Loop

variable {d N n : ℕ}

/-- The **Wilson loop** observable: the trace of the (matrix-valued) Wilson line of a closed
edge list, for a configuration valued in `n × n` complex matrices.  This is the genuine
gauge-invariant Wilson observable; `wilsonLoop_center_smul` below records its centre
eigenvalue. -/
noncomputable def wilsonLoop
    [FiniteLatticeGeometry d N (Matrix (Fin n) (Fin n) ℂ)ˣ]
    (A : GaugeConfig d N (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := (Matrix (Fin n) (Fin n) ℂ)ˣ))) :
    ℂ :=
  (((wilsonLine A es : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)).trace

/-- **Wilson loop under a central edge rescaling.**  Rescaling every edge by a central unit
`z` turns the loop into the trace of `z^L · (line)`:
`wilsonLoop Az es = tr( (z^L) · wilsonLine A es )` (as matrices, `L = es.length`).  This is
the matrix-level centre eigenvalue identity; for a scalar centre element `z = ω·1` the RHS
is `ω^L · tr(wilsonLine A es)`, the `ω^L` eigenvalue that forces the loop expectation to
vanish exactly when a character has `ω^L ≠ 1` (`N ∤ L`), and not otherwise (area law). -/
theorem wilsonLoop_center_smul
    [FiniteLatticeGeometry d N (Matrix (Fin n) (Fin n) ℂ)ˣ]
    {z : (Matrix (Fin n) (Fin n) ℂ)ˣ} (hz : ∀ y, Commute z y)
    (A Az : GaugeConfig d N (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := (Matrix (Fin n) (Fin n) ℂ)ˣ)))
    (hAz : ∀ e, Az e = z * A e) :
    wilsonLoop Az es
      = (((z ^ es.length * wilsonLine A es : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
            Matrix (Fin n) (Fin n) ℂ)).trace := by
  unfold wilsonLoop
  rw [wilsonLine_center_smul hz A Az es hAz]

/-- **Scalar centre element extraction (matrix level).**  The scalar centre matrix `ω•1`
raised to the `L` and multiplied into any matrix `M` pulls the scalar out of the trace as
`ω^L`: `tr( (ω•1)^L * M ) = ω^L · tr M`.  This is the clean algebraic form of the Wilson-loop
centre eigenvalue: combined with `wilsonLoop_center_smul` (whose `z^L·line` is exactly this
shape for `z = ω•1`), it yields `wilsonLoop (scaled) = ω^L · wilsonLoop`, the selection rule
`ω^L ≠ 1 ⟺ N ∤ L`. -/
theorem trace_scalarPow_mul {n : ℕ} (ω : ℂ) (L : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ((ω • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ L * M).trace
      = ω ^ L * M.trace := by
  rw [smul_pow, one_pow, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.one_mul]

/-- **Wilson-loop centre selection rule (algebraic closure).**  If the central unit `z` is
the scalar `ω·1` (`hzval`), then under the diagonal centre rescaling of every edge by `z`,
the Wilson loop is a centre eigenfunction with eigenvalue `ω^L`:
`wilsonLoop Az es = ω^(es.length) · wilsonLoop A es`.

This is the fully algebraic form of the Wilson-loop selection rule: combined with
left-invariance of `gaugeMeasureFrom` under the centre action (the remaining
measure-theoretic step, `HORIZON.md` LG6) and a root of unity `ω` with `ω^L ≠ 1`, it forces
the loop's expectation to vanish exactly when `N ∤ L` — and leaves it free otherwise (the
area-law contributor).  Assembled from `wilsonLine_center_smul` (`z^L` line scaling) and
`trace_scalarPow_mul` (`tr((ω·1)^L·M) = ω^L·tr M`). -/
theorem wilsonLoop_scalarCenter_smul {n : ℕ}
    [FiniteLatticeGeometry d N (Matrix (Fin n) (Fin n) ℂ)ˣ]
    (ω : ℂ) {z : (Matrix (Fin n) (Fin n) ℂ)ˣ}
    (hzval : (z : Matrix (Fin n) (Fin n) ℂ) = ω • (1 : Matrix (Fin n) (Fin n) ℂ))
    (hz : ∀ y, Commute z y)
    (A Az : GaugeConfig d N (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := (Matrix (Fin n) (Fin n) ℂ)ˣ)))
    (hAz : ∀ e, Az e = z * A e) :
    wilsonLoop Az es = ω ^ es.length * wilsonLoop A es := by
  unfold wilsonLoop
  rw [wilsonLine_center_smul hz A Az es hAz, Units.val_mul, Units.val_pow_eq_pow_val,
      hzval, trace_scalarPow_mul]

end Loop

end YangMills.GaugeConfig
