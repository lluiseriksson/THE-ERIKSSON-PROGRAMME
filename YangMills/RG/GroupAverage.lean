/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Balaban's axiomatic group average (gauge-RG campaign, brick B3-full, interface)

`docs/BALABAN-RG-PLAN.md` B3-full.  Bałaban's renormalization-group
averaging of gauge configurations is built on an **axiomatic group
average** `M({U_j})` of a finite set of group elements, and he states
(CMP 109, after eq (0.10)) that all results "are valid universally for
all averages satisfying the above properties."  This is the
source-faithful route to the non-abelian averaging operator `Ū` — it
avoids committing to one explicit (and OCR-fragile) closed form.

**Source.** T. Bałaban, *Renormalization Group Approach to Lattice
Gauge Field Theories. I*, Commun. Math. Phys. **109** (1987) 249–301,
equations (0.5)–(0.10); the explicit Federbush realisation is
P. Federbush (ref. [35] there).  Strategy/framing: Lluis Eriksson,
*The Balaban–Dimock Structural Package* (ai.viXra:2602.0069).

This file formalises the **purely algebraic** part of the interface —
the genuinely group-theoretic axioms, which need no analysis:

* (0.5) inverse-equivariance `M({U_j⁻¹}) = M({U_j})⁻¹`;
* (0.6) bi-equivariance `M({u U_j v}) = u · M({U_j}) · v`;
* (0.7) permutation invariance — **automatic**, the domain is `Multiset G`;
* (0.9) group closure — **automatic**, the codomain is `G`.

The analytic axiom (0.8) — the near-identity linearisation
`(1/i) log M({exp(iA_j)}) = n⁻¹ Σ A_j + O(‖A‖²)`, which ties `M` to the
linear operator `Q` (= `linAvg`, brick B3-linear) — and the Federbush
characterisation (0.10) require a matrix-`log` / near-identity framework
not yet in the core; they are carried as **named obligations** of any
concrete instance (never axioms), to be discharged in a later brick.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

/-- **Bałaban's axiomatic group average** (CMP 109 eqs (0.5)–(0.7),(0.9),
algebraic part): a permutation-invariant (the domain is a `Multiset`),
group-valued (the codomain is `G`, so closure (0.9) is automatic) average
that is inverse-equivariant (0.5) and bi-equivariant (0.6). -/
structure GroupAverage (G : Type*) [Group G] where
  /-- The average of a finite (multi)set of group elements. -/
  M : Multiset G → G
  /-- (0.5) Inverse-equivariance. -/
  inv_eq : ∀ L : Multiset G, M (L.map (·⁻¹)) = (M L)⁻¹
  /-- (0.6) Bi-equivariance. -/
  biequiv : ∀ (u v : G) (L : Multiset G),
    M (L.map (fun U => u * U * v)) = u * M L * v

namespace GroupAverage

variable {G : Type*} [Group G] (A : GroupAverage G)

/-- Left-equivariance (0.6 with `v = 1`). -/
theorem left_equiv (u : G) (L : Multiset G) :
    A.M (L.map (fun U => u * U)) = u * A.M L := by
  have h := A.biequiv u 1 L
  simpa using h

/-- Right-equivariance (0.6 with `u = 1`). -/
theorem right_equiv (v : G) (L : Multiset G) :
    A.M (L.map (fun U => U * v)) = A.M L * v := by
  have h := A.biequiv 1 v L
  simpa using h

/-- **Gauge-covariance seed** (0.6 with `v = u⁻¹`): the average
intertwines conjugation, `M({u U_j u⁻¹}) = u · M({U_j}) · u⁻¹`.  This is
the algebraic root of the gauge covariance of the averaging operator
(brick B4). -/
theorem conj_equiv (u : G) (L : Multiset G) :
    A.M (L.map (fun U => u * U * u⁻¹)) = u * A.M L * u⁻¹ :=
  A.biequiv u u⁻¹ L

end GroupAverage

end YangMills.RG
