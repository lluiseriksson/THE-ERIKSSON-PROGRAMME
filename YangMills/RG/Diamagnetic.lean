/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.MatrixRealization
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Finite-dimensional diamagnetic substrate

This file starts the source-independent, finite-dimensional bookkeeping for the
flow/diamagnetic campaign.  It deliberately stays below the heat-kernel theorem:
the concrete bridge from matrix-valued unitary transports to this linear-isometry
interface is still an open PR1 step.  The point of this module is to make the
killed-region walk convention and the finite isometry-sum estimate available
without using a Frobenius/default matrix norm shortcut.
-/

open scoped BigOperators

namespace YangMills.RG

/-- Endpoint index for an `n`-step finite walk. -/
def finalWalkIndex (n : ℕ) : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

/-- A finite walk whose vertices remain in the killed region `Ω`. -/
structure WalksInside (V : Type*) (Ω : Set V) (x y : V) (n : ℕ) where
  vertex : Fin (n + 1) → V
  start_eq : vertex 0 = x
  stop_eq : vertex (finalWalkIndex n) = y
  inside : ∀ i, vertex i ∈ Ω

namespace WalksInside

/-- The zero-step inside walk, used as the first nonempty sanity witness. -/
def refl {V : Type*} {Ω : Set V} {x : V} (hx : x ∈ Ω) : WalksInside V Ω x x 0 where
  vertex := fun _ => x
  start_eq := rfl
  stop_eq := rfl
  inside := fun _ => hx

end WalksInside

/-- A finite regular ambient graph interface with killed neighbors obtained by
filtering by `Ω`.  The degree is the ambient full degree; killing never changes
the scalar comparison's ambient degree convention. -/
structure FiniteAmbientRegularGraph (V : Type*) where
  neighbor : V → Finset V
  degree : ℕ
  degree_eq : ∀ x, (neighbor x).card = degree

namespace FiniteAmbientRegularGraph

variable {V : Type*} (G : FiniteAmbientRegularGraph V)

/-- Dirichlet-killed neighbor set: keep only ambient neighbors that remain in `Ω`. -/
def killedNeighbors (Ω : Set V) [DecidablePred (· ∈ Ω)] (x : V) : Finset V :=
  (G.neighbor x).filter (fun y => y ∈ Ω)

lemma killedNeighbors_subset (Ω : Set V) [DecidablePred (· ∈ Ω)] (x : V) :
    G.killedNeighbors Ω x ⊆ G.neighbor x := by
  intro y hy
  exact Finset.mem_of_mem_filter y hy

lemma killedNeighbors_card_le_degree (Ω : Set V) [DecidablePred (· ∈ Ω)] (x : V) :
    (G.killedNeighbors Ω x).card ≤ G.degree := by
  rw [← G.degree_eq x]
  exact Finset.card_le_card (G.killedNeighbors_subset Ω x)

end FiniteAmbientRegularGraph

/-- Linear-isometry transport domination for a finite path family: summing one
isometric block contribution over a finite family costs only the number of
paths.  A later PR1 bridge must still convert concrete unitary block matrices
into this `LinearIsometry` interface. -/
theorem norm_sum_linearIsometry_apply_le_card
    {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (s : Finset ι) (T : ι → E →ₛₗᵢ[RingHom.id 𝕜] E) (v : E) :
    ‖∑ i ∈ s, T i v‖ ≤ (s.card : ℝ) * ‖v‖ := by
  calc
    ‖∑ i ∈ s, T i v‖ ≤ ∑ i ∈ s, ‖T i v‖ := norm_sum_le s (fun i => T i v)
    _ = ∑ i ∈ s, ‖v‖ := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact LinearIsometry.norm_map (T i) v
    _ = (s.card : ℝ) * ‖v‖ := by
      rw [Finset.sum_const, nsmul_eq_mul]

end YangMills.RG
