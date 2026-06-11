/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations

/-!
# The lattice chain complex (area law, brick AL1)

`docs/AREA-LAW-PLAN.md` AL1: the `ℤ`-chain complex of the lattice,
abstract over `FiniteLatticeGeometry` —

* `chainBoundary₁` — the boundary of a `1`-chain (edges → vertices):
  `∂₁c(v) = ∑_e c(e)·([dst e = v] − [src e = v])`;
* `plaquetteChain` — the fundamental `1`-chain of a plaquette (its
  four boundary edges, with multiplicity);
* `chainBoundary₂` — the boundary of a `2`-chain (plaquettes → edges);
* `chainBoundary₁_plaquetteChain` — **∂₁(∂p) = 0**: each vertex of
  the square is entered exactly once and left exactly once
  (`plaquetteEdge_src/dst` + the cyclic reindexing `succ4`);
* `chainBoundary₁_comp_chainBoundary₂` — **∂₁ ∘ ∂₂ = 0** by
  linearity.

This is the substrate for `Area(C)` (AL2: the minimal size of a
`2`-chain with boundary `C`) and the spanning-surface lower bound
(AL5).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open FiniteLatticeGeometry

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

open Classical in
/-- The **boundary of a `1`-chain**: signed incidence count at each
vertex. -/
noncomputable def chainBoundary₁
    (c : E (d := d) (N := N) (G := G) → ℤ) : FinBox d N → ℤ :=
  letI := FiniteLatticeGeometry.fintypeE (d := d) (N := N) (G := G)
  fun v => ∑ e : E (d := d) (N := N) (G := G),
    c e * ((if dst e = v then (1 : ℤ) else 0)
      - (if src e = v then (1 : ℤ) else 0))

open Classical in
/-- The **fundamental `1`-chain of a plaquette**: its four boundary
edges, counted with multiplicity. -/
noncomputable def plaquetteChain
    (p : P (d := d) (N := N) (G := G)) :
    E (d := d) (N := N) (G := G) → ℤ :=
  fun e => ∑ i : Fin 4, if plaquetteEdge p i = e then (1 : ℤ) else 0

open Classical in
/-- The **boundary of a `2`-chain**. -/
noncomputable def chainBoundary₂
    (s : P (d := d) (N := N) (G := G) → ℤ) :
    E (d := d) (N := N) (G := G) → ℤ :=
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N) (G := G)
  fun e => ∑ p : P (d := d) (N := N) (G := G), s p * plaquetteChain p e

/-- `succ4` is bijective on `Fin 4`. -/
lemma succ4_bijective : Function.Bijective succ4 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b hab => ?_, rfl⟩
  have ha : (succ4 a).1 = (a.1 + 1) % 4 := rfl
  have hb : (succ4 b).1 = (b.1 + 1) % 4 := rfl
  have h := congrArg Fin.val hab
  rw [ha, hb] at h
  have h4a := a.2
  have h4b := b.2
  exact Fin.ext (by omega)

set_option maxHeartbeats 800000 in
open Classical in
/-- **The boundary of a plaquette's boundary vanishes** — each vertex
of the square is entered once (by the incoming edge) and left once
(by the outgoing edge). -/
theorem chainBoundary₁_plaquetteChain
    (p : P (d := d) (N := N) (G := G)) :
    chainBoundary₁ (d := d) (N := N) (G := G) (plaquetteChain p) = 0 := by
  letI := FiniteLatticeGeometry.fintypeE (d := d) (N := N) (G := G)
  funext v
  show (∑ e : E (d := d) (N := N) (G := G),
      (∑ i : Fin 4, if plaquetteEdge p i = e then (1 : ℤ) else 0) *
        ((if dst e = v then (1 : ℤ) else 0)
          - (if src e = v then (1 : ℤ) else 0))) = 0
  -- distribute and swap the sums
  have hswap : (∑ e : E (d := d) (N := N) (G := G),
      (∑ i : Fin 4, if plaquetteEdge p i = e then (1 : ℤ) else 0) *
        ((if dst e = v then (1 : ℤ) else 0)
          - (if src e = v then (1 : ℤ) else 0)))
      = ∑ i : Fin 4, ∑ e : E (d := d) (N := N) (G := G),
        (if plaquetteEdge p i = e then (1 : ℤ) else 0) *
          ((if dst e = v then (1 : ℤ) else 0)
            - (if src e = v then (1 : ℤ) else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
  rw [hswap]
  -- collapse the inner sum at the unique edge
  have hcollapse : ∀ i : Fin 4,
      (∑ e : E (d := d) (N := N) (G := G),
        (if plaquetteEdge p i = e then (1 : ℤ) else 0) *
          ((if dst e = v then (1 : ℤ) else 0)
            - (if src e = v then (1 : ℤ) else 0)))
      = (if plaquetteVertex p (succ4 i) = v then (1 : ℤ) else 0)
        - (if plaquetteVertex p i = v then (1 : ℤ) else 0) := by
    intro i
    rw [Finset.sum_eq_single (plaquetteEdge p i)
      (fun e _ hne => by rw [if_neg (fun h => hne h.symm), zero_mul])
      (fun habs => absurd (Finset.mem_univ _) habs)]
    rw [if_pos rfl, one_mul, plaquetteEdge_dst, plaquetteEdge_src]
  rw [Finset.sum_congr rfl fun i _ => hcollapse i,
    Finset.sum_sub_distrib]
  -- the two vertex sums agree under the cyclic reindexing
  have hre : (∑ i : Fin 4,
      (if plaquetteVertex p (succ4 i) = v then (1 : ℤ) else 0))
      = ∑ i : Fin 4,
        (if plaquetteVertex p i = v then (1 : ℤ) else 0) :=
    Fintype.sum_bijective succ4 succ4_bijective _ _ (fun i => rfl)
  rw [hre, sub_self]

open Classical in
/-- **∂₁ ∘ ∂₂ = 0:** the lattice chain complex is a complex. -/
theorem chainBoundary₁_comp_chainBoundary₂
    (s : P (d := d) (N := N) (G := G) → ℤ) :
    chainBoundary₁ (d := d) (N := N) (G := G)
      (chainBoundary₂ (d := d) (N := N) (G := G) s) = 0 := by
  letI := FiniteLatticeGeometry.fintypeE (d := d) (N := N) (G := G)
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N) (G := G)
  funext v
  show (∑ e : E (d := d) (N := N) (G := G),
      (∑ p : P (d := d) (N := N) (G := G), s p * plaquetteChain p e) *
        ((if dst e = v then (1 : ℤ) else 0)
          - (if src e = v then (1 : ℤ) else 0))) = 0
  have hswap : (∑ e : E (d := d) (N := N) (G := G),
      (∑ p : P (d := d) (N := N) (G := G), s p * plaquetteChain p e) *
        ((if dst e = v then (1 : ℤ) else 0)
          - (if src e = v then (1 : ℤ) else 0)))
      = ∑ p : P (d := d) (N := N) (G := G), s p *
        ∑ e : E (d := d) (N := N) (G := G), plaquetteChain p e *
          ((if dst e = v then (1 : ℤ) else 0)
            - (if src e = v then (1 : ℤ) else 0)) := by
    calc (∑ e : E (d := d) (N := N) (G := G),
        (∑ p : P (d := d) (N := N) (G := G), s p * plaquetteChain p e) *
          ((if dst e = v then (1 : ℤ) else 0)
            - (if src e = v then (1 : ℤ) else 0)))
        = ∑ e : E (d := d) (N := N) (G := G),
          ∑ p : P (d := d) (N := N) (G := G),
            s p * plaquetteChain p e *
              ((if dst e = v then (1 : ℤ) else 0)
                - (if src e = v then (1 : ℤ) else 0)) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ p : P (d := d) (N := N) (G := G),
          ∑ e : E (d := d) (N := N) (G := G),
            s p * plaquetteChain p e *
              ((if dst e = v then (1 : ℤ) else 0)
                - (if src e = v then (1 : ℤ) else 0)) :=
          Finset.sum_comm
      _ = ∑ p : P (d := d) (N := N) (G := G), s p *
          ∑ e : E (d := d) (N := N) (G := G), plaquetteChain p e *
            ((if dst e = v then (1 : ℤ) else 0)
              - (if src e = v then (1 : ℤ) else 0)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
  rw [hswap]
  refine Finset.sum_eq_zero fun p _ => ?_
  have h := congrFun (chainBoundary₁_plaquetteChain
    (d := d) (N := N) (G := G) p) v
  show s p * _ = 0
  rw [show (∑ e : E (d := d) (N := N) (G := G), plaquetteChain p e *
      ((if dst e = v then (1 : ℤ) else 0)
        - (if src e = v then (1 : ℤ) else 0))) = 0 from h, mul_zero]

end YangMills
