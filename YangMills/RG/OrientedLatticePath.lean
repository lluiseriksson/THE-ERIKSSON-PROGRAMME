/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.HolonomyGauge

/-!
# Bundled oriented lattice paths

This file bundles the existing `IsPathFrom`/`pathEnd` primitives without
replacing them.  It adds concatenation and reversal lemmas, defines a literal
path from one lattice site to another, and delegates its holonomy laws to the
already verified ordered Wilson line.

The convention is fixed throughout: a path `Gamma : OrientedLatticePath a b`
starts at `a`, ends at `b`, and its Wilson line transforms as

`U^g(Gamma) = g(a) U(Gamma) g(b)^{-1}`.

No existence claim is made for an abstract `FiniteLatticeGeometry`; concrete
path construction belongs to the specific periodic-lattice instance.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig

variable {d N : ℕ} {G : Type*} [Group G]
variable [FiniteLatticeGeometry d N G]

abbrev OrientedLatticeEdge :=
  FiniteLatticeGeometry.E (d := d) (N := N) (G := G)

/-- Endpoint of a concatenated edge list. -/
theorem pathEnd_append (a : FinBox d N)
    (es1 es2 : List (OrientedLatticeEdge (d := d) (N := N) (G := G))) :
    pathEnd a (es1 ++ es2) = pathEnd (pathEnd a es1) es2 := by
  induction es1 generalizing a with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, pathEnd_cons]
      exact ih (FiniteLatticeGeometry.dst e)

/-- Connected paths concatenate when the second path starts at the endpoint
of the first. -/
theorem IsPathFrom.append
    {a : FinBox d N}
    {es1 es2 : List (OrientedLatticeEdge (d := d) (N := N) (G := G))}
    (h1 : IsPathFrom a es1) (h2 : IsPathFrom (pathEnd a es1) es2) :
    IsPathFrom a (es1 ++ es2) := by
  induction es1 generalizing a with
  | nil => simpa using h2
  | cons e es ih =>
      obtain ⟨hsrc, hrest⟩ := h1
      exact ⟨hsrc, ih hrest h2⟩

/-- Reverse the order of a path and reverse every oriented edge. -/
def reverseLatticePath
    (es : List (OrientedLatticeEdge (d := d) (N := N) (G := G))) :
    List (OrientedLatticeEdge (d := d) (N := N) (G := G)) :=
  (es.map (FiniteLatticeGeometry.reverse
    (d := d) (N := N) (G := G))).reverse

@[simp] theorem reverseLatticePath_nil :
    reverseLatticePath
      ([] : List (OrientedLatticeEdge (d := d) (N := N) (G := G))) = [] :=
  rfl

theorem reverseLatticePath_cons
    (e : OrientedLatticeEdge (d := d) (N := N) (G := G))
    (es : List (OrientedLatticeEdge (d := d) (N := N) (G := G))) :
    reverseLatticePath (e :: es) =
      reverseLatticePath es ++ [FiniteLatticeGeometry.reverse e] := by
  simp [reverseLatticePath]

/-- Reversal simultaneously gives a connected return path and recovers the
original starting point. -/
theorem reverseLatticePath_spec (a : FinBox d N)
    (es : List (OrientedLatticeEdge (d := d) (N := N) (G := G)))
    (hpath : IsPathFrom a es) :
    IsPathFrom (pathEnd a es) (reverseLatticePath es) ∧
      pathEnd (pathEnd a es) (reverseLatticePath es) = a := by
  induction es generalizing a with
  | nil => simp [reverseLatticePath, IsPathFrom]
  | cons e es ih =>
      obtain ⟨hsrc, hrest⟩ := hpath
      obtain ⟨ihPath, ihEnd⟩ := ih (FiniteLatticeGeometry.dst e) hrest
      rw [reverseLatticePath_cons]
      constructor
      · apply ihPath.append
        rw [ihEnd]
        exact ⟨FiniteLatticeGeometry.src_reverse e, trivial⟩
      · rw [pathEnd_append]
        change pathEnd
          (pathEnd (pathEnd (FiniteLatticeGeometry.dst e) es)
            (reverseLatticePath es))
          [FiniteLatticeGeometry.reverse e] = a
        rw [ihEnd, pathEnd_cons, pathEnd_nil,
          FiniteLatticeGeometry.dst_reverse, hsrc]

/-- Reversing twice returns the original edge list. -/
@[simp] theorem reverseLatticePath_reverseLatticePath
    (es : List (OrientedLatticeEdge (d := d) (N := N) (G := G))) :
    reverseLatticePath (reverseLatticePath es) = es := by
  simp only [reverseLatticePath, List.map_reverse, List.reverse_reverse,
    List.map_map]
  have hfun :
      (FiniteLatticeGeometry.reverse (d := d) (N := N) (G := G) ∘
        FiniteLatticeGeometry.reverse (d := d) (N := N) (G := G)) = id := by
    funext e
    exact FiniteLatticeGeometry.reverse_involutive e
  rw [hfun, List.map_id]

/-- A literal connected oriented lattice path from `a` to `b`. -/
structure OrientedLatticePath (a b : FinBox d N) where
  edges : List (OrientedLatticeEdge (d := d) (N := N) (G := G))
  isPath : IsPathFrom a edges
  ends : pathEnd a edges = b

namespace OrientedLatticePath

variable {a b c : FinBox d N}

/-- The empty path at a site. -/
def refl (a : FinBox d N) : OrientedLatticePath (G := G) a a where
  edges := []
  isPath := trivial
  ends := rfl

/-- Concatenation of literal paths. -/
def trans (Gamma1 : OrientedLatticePath (G := G) a b)
    (Gamma2 : OrientedLatticePath (G := G) b c) :
    OrientedLatticePath (G := G) a c where
  edges := Gamma1.edges ++ Gamma2.edges
  isPath := Gamma1.isPath.append (by simpa [Gamma1.ends] using Gamma2.isPath)
  ends := by rw [pathEnd_append, Gamma1.ends, Gamma2.ends]

/-- The same path traversed backwards. -/
def symm (Gamma : OrientedLatticePath (G := G) a b) :
    OrientedLatticePath (G := G) b a where
  edges := reverseLatticePath Gamma.edges
  isPath := by
    have h := (reverseLatticePath_spec a Gamma.edges Gamma.isPath).1
    simpa [Gamma.ends] using h
  ends := by
    have h := (reverseLatticePath_spec a Gamma.edges Gamma.isPath).2
    simpa [Gamma.ends] using h

/-- Ordered group holonomy of a literal path. -/
def holonomy (Gamma : OrientedLatticePath (G := G) a b)
    (A : GaugeConfig d N G) : G :=
  wilsonLine A Gamma.edges

@[simp] theorem holonomy_refl (a : FinBox d N) (A : GaugeConfig d N G) :
    (refl (G := G) a).holonomy A = 1 :=
  wilsonLine_nil A

theorem holonomy_trans
    (Gamma1 : OrientedLatticePath (G := G) a b)
    (Gamma2 : OrientedLatticePath (G := G) b c)
    (A : GaugeConfig d N G) :
    (Gamma1.trans Gamma2).holonomy A =
      Gamma1.holonomy A * Gamma2.holonomy A :=
  wilsonLine_append A Gamma1.edges Gamma2.edges

theorem holonomy_symm (Gamma : OrientedLatticePath (G := G) a b)
    (A : GaugeConfig d N G) :
    Gamma.symm.holonomy A = (Gamma.holonomy A)⁻¹ :=
  wilsonLine_reverse_list A Gamma.edges

/-- Endpoint gauge covariance of the ordered holonomy. -/
theorem holonomy_gaugeAct (Gamma : OrientedLatticePath (G := G) a b)
    (u : GaugeTransform d N G) (A : GaugeConfig d N G) :
    Gamma.holonomy (GaugeConfig.gaugeAct u A) =
      u a * Gamma.holonomy A * (u b)⁻¹ := by
  change wilsonLine (GaugeConfig.gaugeAct u A) Gamma.edges =
    u a * wilsonLine A Gamma.edges * (u b)⁻¹
  rw [wilsonLine_gaugeAct_path u A Gamma.edges a Gamma.isPath, Gamma.ends]

end OrientedLatticePath

end YangMills.RG
