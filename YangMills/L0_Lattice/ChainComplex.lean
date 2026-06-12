/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations

/-!
# The lattice chain complex (area law, bricks AL1–AL2)

`docs/AREA-LAW-PLAN.md` AL1/AL2: the chain complex of the lattice
over an arbitrary commutative ring `R` — instantiate `R := ℤ` for the
integral theory and `R := ZMod N_c` for the `N`-ality theory that the
edge-balance selection rule (`sunHaarProb_fundMonomial_integral_zero`)
feeds (the AL5 refinement: Haar vanishing is governed mod `N_c`, so
the spanning argument runs mod `N_c` and the resulting bound is the
`N`-ality area).

* `chainBoundary₁` — the boundary of a `1`-chain (edges → vertices);
* `plaquetteChain` — the fundamental `1`-chain of a plaquette;
* `chainBoundary₂` — the boundary of a `2`-chain (plaquettes → edges);
* `chainBoundary₁_plaquetteChain` — `∂₁(∂p) = 0` per plaquette;
* `chainBoundary₁_comp_chainBoundary₂` — **∂₁ ∘ ∂₂ = 0**;
* `chainSupport`, `chainArea` — the minimal discrete spanning surface;
* `chainArea_le`, `exists_minimal_spanning`,
  `chainBoundary₁_eq_zero_of_spans`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open FiniteLatticeGeometry

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]
variable {R : Type*} [CommRing R]

open Classical in
/-- The **boundary of a `1`-chain**: signed incidence count at each
vertex. -/
noncomputable def chainBoundary₁
    (c : E (d := d) (N := N) (G := G) → R) : FinBox d N → R :=
  letI := FiniteLatticeGeometry.fintypeE (d := d) (N := N) (G := G)
  fun v => ∑ e : E (d := d) (N := N) (G := G),
    c e * ((if dst e = v then (1 : R) else 0)
      - (if src e = v then (1 : R) else 0))

open Classical in
/-- The **fundamental `1`-chain of a plaquette**: its four boundary
edges, counted with multiplicity. -/
noncomputable def plaquetteChain
    (p : P (d := d) (N := N) (G := G)) :
    E (d := d) (N := N) (G := G) → R :=
  fun e => ∑ i : Fin 4, if plaquetteEdge p i = e then (1 : R) else 0

open Classical in
/-- The **boundary of a `2`-chain**. -/
noncomputable def chainBoundary₂
    (s : P (d := d) (N := N) (G := G) → R) :
    E (d := d) (N := N) (G := G) → R :=
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
    chainBoundary₁ (d := d) (N := N) (G := G)
      (plaquetteChain (R := R) p) = 0 := by
  letI := FiniteLatticeGeometry.fintypeE (d := d) (N := N) (G := G)
  funext v
  show (∑ e : E (d := d) (N := N) (G := G),
      (∑ i : Fin 4, if plaquetteEdge p i = e then (1 : R) else 0) *
        ((if dst e = v then (1 : R) else 0)
          - (if src e = v then (1 : R) else 0))) = 0
  have hswap : (∑ e : E (d := d) (N := N) (G := G),
      (∑ i : Fin 4, if plaquetteEdge p i = e then (1 : R) else 0) *
        ((if dst e = v then (1 : R) else 0)
          - (if src e = v then (1 : R) else 0)))
      = ∑ i : Fin 4, ∑ e : E (d := d) (N := N) (G := G),
        (if plaquetteEdge p i = e then (1 : R) else 0) *
          ((if dst e = v then (1 : R) else 0)
            - (if src e = v then (1 : R) else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
  rw [hswap]
  have hcollapse : ∀ i : Fin 4,
      (∑ e : E (d := d) (N := N) (G := G),
        (if plaquetteEdge p i = e then (1 : R) else 0) *
          ((if dst e = v then (1 : R) else 0)
            - (if src e = v then (1 : R) else 0)))
      = (if plaquetteVertex p (succ4 i) = v then (1 : R) else 0)
        - (if plaquetteVertex p i = v then (1 : R) else 0) := by
    intro i
    rw [Finset.sum_eq_single (plaquetteEdge p i)
      (fun e _ hne => by rw [if_neg (fun h => hne h.symm), zero_mul])
      (fun habs => absurd (Finset.mem_univ _) habs)]
    rw [if_pos rfl, one_mul, plaquetteEdge_dst, plaquetteEdge_src]
  rw [Finset.sum_congr rfl fun i _ => hcollapse i,
    Finset.sum_sub_distrib]
  have hre : (∑ i : Fin 4,
      (if plaquetteVertex p (succ4 i) = v then (1 : R) else 0))
      = ∑ i : Fin 4,
        (if plaquetteVertex p i = v then (1 : R) else 0) :=
    Fintype.sum_bijective succ4 succ4_bijective _ _ (fun i => rfl)
  rw [hre, sub_self]

open Classical in
/-- **∂₁ ∘ ∂₂ = 0:** the lattice chain complex is a complex, over any
commutative ring. -/
theorem chainBoundary₁_comp_chainBoundary₂
    (s : P (d := d) (N := N) (G := G) → R) :
    chainBoundary₁ (d := d) (N := N) (G := G)
      (chainBoundary₂ (d := d) (N := N) (G := G) s) = 0 := by
  letI := FiniteLatticeGeometry.fintypeE (d := d) (N := N) (G := G)
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N) (G := G)
  funext v
  show (∑ e : E (d := d) (N := N) (G := G),
      (∑ p : P (d := d) (N := N) (G := G), s p * plaquetteChain p e) *
        ((if dst e = v then (1 : R) else 0)
          - (if src e = v then (1 : R) else 0))) = 0
  have hswap : (∑ e : E (d := d) (N := N) (G := G),
      (∑ p : P (d := d) (N := N) (G := G), s p * plaquetteChain p e) *
        ((if dst e = v then (1 : R) else 0)
          - (if src e = v then (1 : R) else 0)))
      = ∑ p : P (d := d) (N := N) (G := G), s p *
        ∑ e : E (d := d) (N := N) (G := G), plaquetteChain p e *
          ((if dst e = v then (1 : R) else 0)
            - (if src e = v then (1 : R) else 0)) := by
    calc (∑ e : E (d := d) (N := N) (G := G),
        (∑ p : P (d := d) (N := N) (G := G), s p * plaquetteChain p e) *
          ((if dst e = v then (1 : R) else 0)
            - (if src e = v then (1 : R) else 0)))
        = ∑ e : E (d := d) (N := N) (G := G),
          ∑ p : P (d := d) (N := N) (G := G),
            s p * plaquetteChain p e *
              ((if dst e = v then (1 : R) else 0)
                - (if src e = v then (1 : R) else 0)) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ p : P (d := d) (N := N) (G := G),
          ∑ e : E (d := d) (N := N) (G := G),
            s p * plaquetteChain p e *
              ((if dst e = v then (1 : R) else 0)
                - (if src e = v then (1 : R) else 0)) :=
          Finset.sum_comm
      _ = ∑ p : P (d := d) (N := N) (G := G), s p *
          ∑ e : E (d := d) (N := N) (G := G), plaquetteChain p e *
            ((if dst e = v then (1 : R) else 0)
              - (if src e = v then (1 : R) else 0)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
  rw [hswap]
  refine Finset.sum_eq_zero fun p _ => ?_
  have h := congrFun (chainBoundary₁_plaquetteChain
    (d := d) (N := N) (G := G) (R := R) p) v
  show s p * _ = 0
  rw [show (∑ e : E (d := d) (N := N) (G := G),
      plaquetteChain (R := R) p e *
      ((if dst e = v then (1 : R) else 0)
        - (if src e = v then (1 : R) else 0))) = 0 from h, mul_zero]

/-! ### Area (brick AL2): the minimal size of a spanning surface -/

open Classical in
/-- The **support** of a `2`-chain: the plaquettes it uses. -/
noncomputable def chainSupport (s : P (d := d) (N := N) (G := G) → R) :
    Finset (P (d := d) (N := N) (G := G)) :=
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N) (G := G)
  Finset.univ.filter (fun p => s p ≠ 0)

open Classical in
/-- The **area of a `1`-chain**: the minimal support size of a
`2`-chain whose boundary is `c` (the minimal discrete spanning
surface).  Over `R := ZMod N_c` this is the `N`-ality area.  Junk
value `0` for unspannable chains; all lemmas guard with
spannability. -/
noncomputable def chainArea
    (c : E (d := d) (N := N) (G := G) → R) : ℕ :=
  sInf {n : ℕ | ∃ s : P (d := d) (N := N) (G := G) → R,
    chainBoundary₂ (d := d) (N := N) (G := G) s = c ∧
      (chainSupport (d := d) (N := N) (G := G) s).card = n}

open Classical in
/-- **The defining upper bound:** every spanning surface witnesses the
area — `Area(∂₂s) ≤ |supp s|`.  This is the inequality the area-law
expansion consumes (AL5): a nonvanishing term of size `|S|` yields a
spanning `2`-chain supported in `S`, hence `Area(C) ≤ |S|`. -/
theorem chainArea_le {c : E (d := d) (N := N) (G := G) → R}
    {s : P (d := d) (N := N) (G := G) → R}
    (h : chainBoundary₂ (d := d) (N := N) (G := G) s = c) :
    chainArea (d := d) (N := N) (G := G) c
      ≤ (chainSupport (d := d) (N := N) (G := G) s).card :=
  Nat.sInf_le ⟨s, h, rfl⟩

open Classical in
/-- **Attainment:** a spannable chain has a minimal spanning surface. -/
theorem exists_minimal_spanning
    {c : E (d := d) (N := N) (G := G) → R}
    (h : ∃ s : P (d := d) (N := N) (G := G) → R,
      chainBoundary₂ (d := d) (N := N) (G := G) s = c) :
    ∃ s : P (d := d) (N := N) (G := G) → R,
      chainBoundary₂ (d := d) (N := N) (G := G) s = c ∧
        (chainSupport (d := d) (N := N) (G := G) s).card
          = chainArea (d := d) (N := N) (G := G) c := by
  obtain ⟨s₀, hs₀⟩ := h
  have hne : {n : ℕ | ∃ s : P (d := d) (N := N) (G := G) → R,
      chainBoundary₂ (d := d) (N := N) (G := G) s = c ∧
        (chainSupport (d := d) (N := N) (G := G) s).card = n}.Nonempty :=
    ⟨_, s₀, hs₀, rfl⟩
  obtain ⟨s, hs, hcard⟩ := Nat.sInf_mem hne
  exact ⟨s, hs, hcard⟩

open Classical in
/-- **Spannable chains are closed:** `∂₁c = 0` whenever `c = ∂₂s` —
the necessary condition that Wilson loops (closed `1`-chains) satisfy
and open lines violate. -/
theorem chainBoundary₁_eq_zero_of_spans
    {c : E (d := d) (N := N) (G := G) → R}
    (h : ∃ s : P (d := d) (N := N) (G := G) → R,
      chainBoundary₂ (d := d) (N := N) (G := G) s = c) :
    chainBoundary₁ (d := d) (N := N) (G := G) c = 0 := by
  obtain ⟨s, hs⟩ := h
  rw [← hs]
  exact chainBoundary₁_comp_chainBoundary₂ (d := d) (N := N) (G := G) s

open Classical in
/-- **AL5 interface, support-monotone form:** a spanning `2`-chain
supported inside a plaquette set `S` bounds the area by `|S|`.  This
is the exact shape the expansion consumes: a non-vanishing term
indexed by `S ⊆ plaquettes` produces (via edge balance) a `ZMod N_c`
chain supported in `S` whose boundary is the loop chain, whence
`Area(C) ≤ |S|`. -/
theorem chainArea_le_card_of_support_subset
    {c : E (d := d) (N := N) (G := G) → R}
    {s : P (d := d) (N := N) (G := G) → R}
    {S : Finset (P (d := d) (N := N) (G := G))}
    (h : chainBoundary₂ (d := d) (N := N) (G := G) s = c)
    (hsupp : chainSupport (d := d) (N := N) (G := G) s ⊆ S) :
    chainArea (d := d) (N := N) (G := G) c ≤ S.card :=
  le_trans (chainArea_le (d := d) (N := N) (G := G) h)
    (Finset.card_le_card hsupp)

open Classical in
/-- The **restriction of a `2`-chain to a plaquette set** — the
coefficient chain a non-vanishing expansion term carries. -/
noncomputable def indicatorChain
    (S : Finset (P (d := d) (N := N) (G := G)))
    (σ : P (d := d) (N := N) (G := G) → R) :
    P (d := d) (N := N) (G := G) → R :=
  fun p => if p ∈ S then σ p else 0

open Classical in
/-- The restricted chain is supported in `S`. -/
theorem chainSupport_indicatorChain_subset
    (S : Finset (P (d := d) (N := N) (G := G)))
    (σ : P (d := d) (N := N) (G := G) → R) :
    chainSupport (d := d) (N := N) (G := G)
      (indicatorChain (d := d) (N := N) (G := G) S σ) ⊆ S := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N) (G := G)
  intro p hp
  have hmem : p ∈ Finset.univ.filter
      (fun q => indicatorChain (d := d) (N := N) (G := G) S σ q ≠ 0) := hp
  have hne := (Finset.mem_filter.mp hmem).2
  by_contra hnot
  exact hne (if_neg hnot)

open Classical in
/-- The **`1`-chain of a Wilson path**: each traversed edge counted
`+1`, antisymmetrized against the reversed orientation.  This is the
orientation-odd representative — the object whose spanning surface
the area law measures (TE-2 of the AL4.5 join,
`docs/AREA-LAW-PLAN.md` §4). -/
noncomputable def loopChain
    (es : List (E (d := d) (N := N) (G := G))) :
    E (d := d) (N := N) (G := G) → R :=
  fun e => (es.count e : R) - (es.count (reverse e) : R)

open Classical in
@[simp] theorem loopChain_nil :
    loopChain (R := R) ([] : List (E (d := d) (N := N) (G := G))) = 0 := by
  funext e
  simp [loopChain]

open Classical in
/-- The loop chain is **orientation-odd**: reversing the probe edge
flips the sign. -/
theorem loopChain_reverse
    (es : List (E (d := d) (N := N) (G := G)))
    (e : E (d := d) (N := N) (G := G)) :
    loopChain (R := R) es (reverse e) = - loopChain (R := R) es e := by
  simp only [loopChain, reverse_involutive e]
  ring

open Classical in
/-- The loop chain is **additive under path concatenation** — Wilson
lines compose, and so do their chains. -/
theorem loopChain_append
    (es₁ es₂ : List (E (d := d) (N := N) (G := G))) :
    loopChain (R := R) (es₁ ++ es₂)
      = fun e => loopChain (R := R) es₁ e + loopChain (R := R) es₂ e := by
  funext e
  simp only [loopChain, List.count_append, Nat.cast_add]
  ring

open Classical in
/-- **The plaquette's Wilson list and its chain** (area-law assembly):
the `1`-chain of the plaquette's 4-edge Wilson list is the
ANTISYMMETRIZED plaquette chain — forward incidences minus
reverse incidences. -/
theorem loopChain_plaquette_list (p : P (d := d) (N := N) (G := G))
    (e : E (d := d) (N := N) (G := G)) :
    loopChain (R := R) (d := d) (N := N) (G := G)
        [plaquetteEdge p 0, plaquetteEdge p 1,
         plaquetteEdge p 2, plaquetteEdge p 3] e
      = plaquetteChain (R := R) p e
          - plaquetteChain (R := R) p (reverse e) := by
  have hcount : ∀ x : E (d := d) (N := N) (G := G),
      (([plaquetteEdge p 0, plaquetteEdge p 1, plaquetteEdge p 2,
        plaquetteEdge p 3].count x : R))
        = ∑ i : Fin 4, if plaquetteEdge p i = x then (1 : R) else 0 := by
    intro x
    rw [Fin.sum_univ_four]
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    push_cast
    by_cases h0 : plaquetteEdge p 0 = x <;>
      by_cases h1 : plaquetteEdge p 1 = x <;>
        by_cases h2 : plaquetteEdge p 2 = x <;>
          by_cases h3 : plaquetteEdge p 3 = x <;>
            simp [h0, h1, h2, h3, eq_comm] <;> ring
  calc loopChain (R := R) (d := d) (N := N) (G := G)
        [plaquetteEdge p 0, plaquetteEdge p 1,
         plaquetteEdge p 2, plaquetteEdge p 3] e
      = (([plaquetteEdge p 0, plaquetteEdge p 1, plaquetteEdge p 2,
          plaquetteEdge p 3].count e : R))
        - (([plaquetteEdge p 0, plaquetteEdge p 1, plaquetteEdge p 2,
          plaquetteEdge p 3].count
            (reverse (d := d) (N := N) (G := G) e) : R)) := rfl
    _ = (∑ i : Fin 4, if plaquetteEdge p i = e then (1 : R) else 0)
        - ∑ i : Fin 4, if plaquetteEdge p i
            = reverse (d := d) (N := N) (G := G) e then (1 : R) else 0 := by
        rw [hcount e, hcount (reverse e)]
    _ = plaquetteChain (R := R) p e
        - plaquetteChain (R := R) p (reverse e) := rfl

open Classical in
/-- **Coefficient combinations of plaquette Wilson lists are the
antisymmetrized `∂₂`** — the chain-equation form the multi-line
selection rule (`integral_prod_trace_wilsonLine_eq_zero_of_sum_
loopChain_ne_zero`) produces for the family
`loop :: plaquette-loops-of-S`. -/
theorem sum_mul_loopChain_plaquette_list
    (σ : P (d := d) (N := N) (G := G) → R)
    (e : E (d := d) (N := N) (G := G)) :
    (letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N) (G := G)
      ∑ p : P (d := d) (N := N) (G := G),
        σ p * loopChain (R := R) (d := d) (N := N) (G := G)
          [plaquetteEdge p 0, plaquetteEdge p 1,
           plaquetteEdge p 2, plaquetteEdge p 3] e)
      = chainBoundary₂ (d := d) (N := N) (G := G) σ e
          - chainBoundary₂ (d := d) (N := N) (G := G) σ
              (reverse (d := d) (N := N) (G := G) e) := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N) (G := G)
  rw [Finset.sum_congr rfl fun p _ => by
    rw [loopChain_plaquette_list (R := R) p e, mul_sub]]
  rw [Finset.sum_sub_distrib]
  rfl

/-! ## The antisymmetrized boundary and its area (area-law assembly ii)

The Wilson-loop selection rules are orientation-odd — a backward
traversal contributes the conjugate.  The chain object they produce is
therefore the ANTISYMMETRIZED boundary (forward minus reverse
incidence), and the area-law's spanning bound runs against it.  The
ladder below replays `chainArea`/`chainArea_le` verbatim for it. -/

open Classical in
/-- The **antisymmetrized boundary of a `2`-chain**: forward minus
reverse incidence — `∑_p σ_p·loopChain(plaquette p)` in closed form
(`sum_mul_loopChain_plaquette_list`). -/
noncomputable def chainBoundary₂A
    (s : P (d := d) (N := N) (G := G) → R) :
    E (d := d) (N := N) (G := G) → R :=
  fun e => chainBoundary₂ (d := d) (N := N) (G := G) s e
    - chainBoundary₂ (d := d) (N := N) (G := G) s
        (reverse (d := d) (N := N) (G := G) e)

open Classical in
/-- The selection-rule form of `sum_mul_loopChain_plaquette_list`:
plaquette Wilson-list combinations ARE the antisymmetrized
boundary. -/
theorem sum_mul_loopChain_plaquette_list_eq_chainBoundary₂A
    (σ : P (d := d) (N := N) (G := G) → R)
    (e : E (d := d) (N := N) (G := G)) :
    (letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N) (G := G)
      ∑ p : P (d := d) (N := N) (G := G),
        σ p * loopChain (R := R) (d := d) (N := N) (G := G)
          [plaquetteEdge p 0, plaquetteEdge p 1,
           plaquetteEdge p 2, plaquetteEdge p 3] e)
      = chainBoundary₂A (d := d) (N := N) (G := G) σ e :=
  sum_mul_loopChain_plaquette_list (R := R) σ e

open Classical in
/-- The **`N`-ality area of a `1`-chain**: the minimal support size of
a `2`-chain whose ANTISYMMETRIZED boundary is `c`.  Junk value `0` for
unspannable chains; all lemmas guard with spannability. -/
noncomputable def chainAreaA
    (c : E (d := d) (N := N) (G := G) → R) : ℕ :=
  sInf {n : ℕ | ∃ s : P (d := d) (N := N) (G := G) → R,
    chainBoundary₂A (d := d) (N := N) (G := G) s = c ∧
      (chainSupport (d := d) (N := N) (G := G) s).card = n}

open Classical in
/-- **The defining upper bound** for the antisymmetrized area. -/
theorem chainAreaA_le {c : E (d := d) (N := N) (G := G) → R}
    {s : P (d := d) (N := N) (G := G) → R}
    (h : chainBoundary₂A (d := d) (N := N) (G := G) s = c) :
    chainAreaA (d := d) (N := N) (G := G) c
      ≤ (chainSupport (d := d) (N := N) (G := G) s).card :=
  Nat.sInf_le ⟨s, h, rfl⟩

open Classical in
/-- **The AL5 interface, antisymmetrized form:** a spanning `2`-chain
supported inside a plaquette set `S` bounds the `N`-ality area by
`|S|` — the inequality the surviving strong-coupling expansion terms
feed. -/
theorem chainAreaA_le_card_of_support_subset
    {c : E (d := d) (N := N) (G := G) → R}
    {s : P (d := d) (N := N) (G := G) → R}
    {S : Finset (P (d := d) (N := N) (G := G))}
    (h : chainBoundary₂A (d := d) (N := N) (G := G) s = c)
    (hsupp : chainSupport (d := d) (N := N) (G := G) s ⊆ S) :
    chainAreaA (d := d) (N := N) (G := G) c ≤ S.card :=
  le_trans (chainAreaA_le (d := d) (N := N) (G := G) h)
    (Finset.card_le_card hsupp)

open Classical in
/-- **Reversing a Wilson path negates its chain** — traversing the
list backwards with reversed edges (`conj tr U = tr U†` at the
holonomy level) flips every signed incidence. -/
theorem loopChain_reverse_list (l : List (E (d := d) (N := N) (G := G)))
    (e : E (d := d) (N := N) (G := G)) :
    loopChain (R := R) (d := d) (N := N) (G := G)
        ((l.map (reverse (d := d) (N := N) (G := G))).reverse) e
      = - loopChain (R := R) (d := d) (N := N) (G := G) l e := by
  have hinj : Function.Injective (reverse (d := d) (N := N) (G := G)) :=
    fun a b hab => by
      rw [← reverse_involutive (d := d) (N := N) (G := G) a, hab,
        reverse_involutive]
  have h1 : ((l.map (reverse (d := d) (N := N) (G := G))).reverse).count e
      = l.count (reverse (d := d) (N := N) (G := G) e) := by
    rw [List.count_reverse]
    conv_lhs => rw [← reverse_involutive (d := d) (N := N) (G := G) e]
    exact List.count_map_of_injective l _ hinj _
  have h2 : ((l.map (reverse (d := d) (N := N) (G := G))).reverse).count
      (reverse (d := d) (N := N) (G := G) e) = l.count e := by
    rw [List.count_reverse]
    exact List.count_map_of_injective l _ hinj _
  unfold loopChain
  rw [h1, h2]
  ring

open Classical in
/-- The antisymmetrized boundary is `R`-linear in the sign:
`∂₂A(−s) = −∂₂A s`. -/
theorem chainBoundary₂A_neg (s : P (d := d) (N := N) (G := G) → R) :
    chainBoundary₂A (d := d) (N := N) (G := G) (fun p => - s p)
      = fun e => - chainBoundary₂A (d := d) (N := N) (G := G) s e := by
  funext e
  unfold chainBoundary₂A chainBoundary₂
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

open Classical in
/-- Negating the coefficients preserves the support. -/
theorem chainSupport_neg (s : P (d := d) (N := N) (G := G) → R) :
    chainSupport (d := d) (N := N) (G := G) (fun p => - s p)
      = chainSupport (d := d) (N := N) (G := G) s := by
  unfold chainSupport
  exact Finset.filter_congr fun p _ => by simp

open Classical in
/-- **The `N`-ality area is orientation-blind:** negating the target
chain — e.g. the sign mismatch between `loopChain C` and the chain
equation's `−loopChain C` — does not change the area. -/
theorem chainAreaA_neg (c : E (d := d) (N := N) (G := G) → R) :
    chainAreaA (d := d) (N := N) (G := G) (fun e => - c e)
      = chainAreaA (d := d) (N := N) (G := G) c := by
  unfold chainAreaA
  congr 1
  ext n
  constructor
  · rintro ⟨s, hs, hcard⟩
    refine ⟨fun p => - s p, ?_, by
      rw [chainSupport_neg (d := d) (N := N) (G := G), hcard]⟩
    rw [chainBoundary₂A_neg (d := d) (N := N) (G := G), hs]
    funext e
    simp
  · rintro ⟨s, hs, hcard⟩
    refine ⟨fun p => - s p, ?_, by
      rw [chainSupport_neg (d := d) (N := N) (G := G), hcard]⟩
    rw [chainBoundary₂A_neg (d := d) (N := N) (G := G), hs]

end YangMills
