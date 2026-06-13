/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Balaban's axiomatic group average (gauge-RG campaign, brick B3-full, interface)

`docs/BALABAN-RG-PLAN.md` B3-full.  Bałaban's renormalization-group
averaging of gauge configurations is built on an **axiomatic group
average** `M({U_j})` of a finite NONEMPTY set of group elements, and he
states (CMP 109, after eq (0.10)) that all results "are valid universally
for all averages satisfying the above properties."

**Source.** T. Bałaban, *Renormalization Group Approach to Lattice
Gauge Field Theories. I*, Commun. Math. Phys. **109** (1987) 249–301,
equations (0.5)–(0.10); the explicit realisation is P. Federbush,
*A phase cell approach to Yang–Mills theory* (ref. [35] there).
Strategy/framing: Lluis Eriksson, *The Balaban–Dimock Structural
Package* (ai.viXra:2602.0069).

Axioms formalised (the purely algebraic part — no analysis needed):

* (0.5) inverse-equivariance `M({U_j⁻¹}) = M({U_j})⁻¹`;
* (0.6) bi-equivariance `M({u U_j v}) = u · M({U_j}) · v`;
* (0.7) permutation invariance — **automatic**, the domain is `Multiset G`;
* (0.9) group closure — **automatic**, the codomain is `G`.

**Honesty fix (2026-06-12).**  The axioms are stated for NONEMPTY
multisets (`L ≠ 0`).  This is essential and source-faithful: Bałaban's
`M` averages `{U_j : j = 1,…,n}` with `n ≥ 1`, and (0.6) on the empty
multiset would read `M(∅) = u·M(∅)·v` for all `u,v`, which forces the
group to be trivial — i.e. the unrestricted interface is *unsatisfiable*
for `SU(N)`, hence vacuous.  With the `L ≠ 0` restriction the interface
is genuinely inhabited: `meanAverage` below realises it for the abelian
prototype (and exhibits the exact linearisation (0.8)).

The analytic axiom (0.8) — the near-identity linearisation
`(1/i) log M({exp(iA_j)}) = n⁻¹ Σ A_j + O(‖A‖²)`, tying `M` to the linear
operator `Q` (= `linAvg`) — holds EXACTLY (no higher-order terms) for
the abelian inhabitant; the non-abelian case and the operator `Ū`
(CMP 109 (0.12)) need a near-identity matrix-`log` framework and are the
next sub-brick.  Oracle target: `[propext, Classical.choice,
Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

/-- **Bałaban's axiomatic group average** (CMP 109 eqs (0.5)–(0.7),(0.9),
algebraic part), on NONEMPTY finite multisets: a permutation-invariant
(the domain is a `Multiset`), group-valued (closure (0.9) automatic)
average that is inverse-equivariant (0.5) and bi-equivariant (0.6). -/
structure GroupAverage (G : Type*) [Group G] where
  /-- The average of a finite nonempty (multi)set of group elements. -/
  M : Multiset G → G
  /-- (0.5) Inverse-equivariance, on nonempty multisets. -/
  inv_eq : ∀ L : Multiset G, L ≠ 0 → M (L.map (·⁻¹)) = (M L)⁻¹
  /-- (0.6) Bi-equivariance, on nonempty multisets. -/
  biequiv : ∀ (u v : G) (L : Multiset G), L ≠ 0 →
    M (L.map (fun U => u * U * v)) = u * M L * v

namespace GroupAverage

variable {G : Type*} [Group G] (A : GroupAverage G)

/-- Left-equivariance (0.6 with `v = 1`). -/
theorem left_equiv (u : G) {L : Multiset G} (hL : L ≠ 0) :
    A.M (L.map (fun U => u * U)) = u * A.M L := by
  have h := A.biequiv u 1 L hL
  simpa using h

/-- Right-equivariance (0.6 with `u = 1`). -/
theorem right_equiv (v : G) {L : Multiset G} (hL : L ≠ 0) :
    A.M (L.map (fun U => U * v)) = A.M L * v := by
  have h := A.biequiv 1 v L hL
  simpa using h

/-- **Gauge-covariance seed** (0.6 with `v = u⁻¹`): the average
intertwines conjugation, `M({u U_j u⁻¹}) = u · M({U_j}) · u⁻¹` — the
algebraic root of the gauge covariance of the averaging operator (B4). -/
theorem conj_equiv (u : G) {L : Multiset G} (hL : L ≠ 0) :
    A.M (L.map (fun U => u * U * u⁻¹)) = u * A.M L * u⁻¹ :=
  A.biequiv u u⁻¹ L hL

end GroupAverage

/-! ## Non-vacuity: the abelian arithmetic mean inhabits the interface -/

open Multiplicative in
/-- **The interface is inhabited** (non-vacuity certificate): for the
abelian prototype `G = Multiplicative V` (`V` a real vector space) the
arithmetic mean `M(L) = (#L)⁻¹ · Σ_j A_j` satisfies all the axioms.  In
additive (Lie-algebra) terms this is exactly the linear average, so the
linearisation (0.8) holds with no higher-order terms. -/
noncomputable def meanAverage (V : Type*) [AddCommGroup V] [Module ℝ V] :
    GroupAverage (Multiplicative V) where
  M := fun L => Multiplicative.ofAdd
    ((L.card : ℝ)⁻¹ • (L.map Multiplicative.toAdd).sum)
  inv_eq := by
    intro L hL
    have hsum : (Multiset.map Multiplicative.toAdd (L.map (·⁻¹))).sum
        = -(L.map Multiplicative.toAdd).sum := by
      rw [Multiset.map_map]
      have hcomp : (Multiplicative.toAdd ∘
          (Inv.inv : Multiplicative V → Multiplicative V))
          = fun U => -(Multiplicative.toAdd U) := by funext U; simp
      rw [hcomp, Multiset.sum_map_neg]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_inv, Multiset.card_map, hsum, smul_neg]
  biequiv := by
    intro u v L hL
    have hc : (L.card : ℝ) ≠ 0 := by
      simpa [Multiset.card_eq_zero] using hL
    have hsum : (Multiset.map Multiplicative.toAdd
          (L.map (fun U => u * U * v))).sum
        = L.card • (Multiplicative.toAdd u + Multiplicative.toAdd v)
          + (L.map Multiplicative.toAdd).sum := by
      rw [Multiset.map_map]
      have hcomp : (Multiplicative.toAdd ∘ fun U => u * U * v)
          = fun U => (Multiplicative.toAdd u + Multiplicative.toAdd v)
              + Multiplicative.toAdd U := by
        funext U; simp only [Function.comp_apply, toAdd_mul]; abel
      rw [hcomp, Multiset.sum_map_add, Multiset.map_const',
        Multiset.sum_replicate]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul, Multiset.card_map, hsum]
    rw [← Nat.cast_smul_eq_nsmul ℝ L.card (Multiplicative.toAdd u +
      Multiplicative.toAdd v), smul_add, smul_smul, inv_mul_cancel₀ hc,
      one_smul]
    abel

end YangMills.RG
