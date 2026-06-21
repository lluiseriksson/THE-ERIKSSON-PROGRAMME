/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# T2 step (ii) — the abstract tree-walk bound

The last open step of `kp_per_size_bound` (`docs/WALK-BOUND-PLAN.md`): summing
a tree-structured product of pair factors over all assignments, where each
factor couples a vertex to its parent, is bounded by `Aⁿ · ∑ w` whenever every
conditional neighbour sum is bounded by `A` (the KP neighbour estimate).

The vertex type is abstract so that leaf removal is a plain induction on `n`:
the function space splits at a maximal-level vertex (`Equiv.funSplitAt`),
whose factor is the only one reading that coordinate (it is nobody's parent),
and the inner sum is exactly the `A`-bound.

Instantiation (assembly step, see the plan): `V := Fin (m+1)`, `r := 0`,
`p := bfsParent T`, `lev := bfsLevel T`, `w := ‖activity ·‖`,
`I x y := if incomp x y then 1 else 0`, `A ≥ max a`, with
`prod_tree_eq_prod_parents` converting tree-edge products to this
parent-indexed form and `kp_neighbor_sum_le` supplying the hypothesis.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

/-- **The tree-walk bound.**  If the parent map `p` strictly decreases a level
function away from the root `r`, all factors are nonnegative, and every
conditional neighbour sum obeys `∑ y, I x y * w y ≤ A`, then
`∑_X (∏_{v ≠ r} I(X_{p v}, X_v)·w(X_v))·w(X_r) ≤ Aⁿ · ∑ y, w y`
on a vertex type of cardinality `n + 1`. -/
theorem tree_walk_bound (n : ℕ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (β : Type*) [Fintype β]
      (r : V) (p : V → V) (lev : V → ℕ)
      (I : β → β → ℝ) (w : β → ℝ) (A : ℝ),
      Fintype.card V = n + 1 →
      (∀ v, v ≠ r → lev (p v) < lev v) →
      (∀ x y, 0 ≤ I x y) → (∀ y, 0 ≤ w y) → 0 ≤ A →
      (∀ x : β, ∑ y, I x y * w y ≤ A) →
      ∑ X : V → β,
        (∏ v ∈ Finset.univ.filter (fun v => v ≠ r),
          I (X (p v)) (X v) * w (X v)) * w (X r)
        ≤ A ^ n * ∑ y, w y := by
  induction n with
  | zero =>
    intro V _ _ β _ r p lev I w A hcard hdesc hI hw hA hsum
    have hsub : Subsingleton V :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hfil : Finset.univ.filter (fun v : V => v ≠ r) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v _
      simp [Subsingleton.elim v r]
    rw [hfil]
    simp only [Finset.prod_empty, one_mul, pow_zero]
    refine le_of_eq (Fintype.sum_bijective (fun X : V → β => X r)
      ⟨?_, ?_⟩ _ _ (fun X => rfl))
    · intro X Y h
      funext v
      rw [Subsingleton.elim v r]
      exact h
    · intro y
      exact ⟨fun _ => y, rfl⟩
  | succ n ih =>
    intro V _ _ β _ r p lev I w A hcard hdesc hI hw hA hsum
    classical
    -- a nonroot vertex of maximal level: necessarily a leaf
    have hne : (Finset.univ.filter (fun v : V => v ≠ r)).Nonempty := by
      have h1 : 1 < Fintype.card V := by omega
      obtain ⟨v, hv⟩ := Fintype.exists_ne_of_one_lt_card h1 r
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
    obtain ⟨v₀, hv₀mem, hv₀max⟩ :=
      Finset.exists_max_image (Finset.univ.filter (fun v : V => v ≠ r)) lev hne
    have hv₀r : v₀ ≠ r := (Finset.mem_filter.mp hv₀mem).2
    have hleaf : ∀ v : V, v ≠ r → p v ≠ v₀ := by
      intro v hvr hpv
      have h1 := hdesc v hvr
      rw [hpv] at h1
      have h2 := hv₀max v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvr⟩)
      omega
    have hpv₀ : p v₀ ≠ v₀ := by
      intro h
      have h1 := hdesc v₀ hv₀r
      rw [h] at h1
      omega
    have hrv₀ : r ≠ v₀ := Ne.symm hv₀r
    -- the reduced vertex type
    have hcard' : Fintype.card {j : V // j ≠ v₀} = n + 1 := by
      rw [Fintype.card_subtype, Finset.filter_ne',
        Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ]
      omega
    set r' : {j : V // j ≠ v₀} := ⟨r, hrv₀⟩ with hr'def
    set p' : {j : V // j ≠ v₀} → {j : V // j ≠ v₀} :=
      fun v => if h : p v.1 = v₀ then r' else ⟨p v.1, h⟩ with hp'def
    have hdesc' : ∀ v : {j : V // j ≠ v₀}, v ≠ r' →
        lev (p' v).1 < lev v.1 := by
      intro v hvr'
      have hv1r : v.1 ≠ r := by
        intro h
        exact hvr' (Subtype.ext h)
      have hpne : p v.1 ≠ v₀ := hleaf v.1 hv1r
      have hpeq : p' v = ⟨p v.1, hpne⟩ := by
        simp only [hp'def]
        rw [dif_neg hpne]
      rw [hpeq]
      exact hdesc v.1 hv1r
    -- split the function space at the leaf
    set e := Equiv.funSplitAt v₀ β with hedef
    have heval₀ : ∀ (y : β) (X' : {j : V // j ≠ v₀} → β),
        e.symm (y, X') v₀ = y := by
      intro y X'
      simp [hedef]
    have hevalne : ∀ (y : β) (X' : {j : V // j ≠ v₀} → β) (j : V)
        (hj : j ≠ v₀), e.symm (y, X') j = X' ⟨j, hj⟩ := by
      intro y X' j hj
      simp [hedef, hj]
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
    -- pointwise bound in the remaining coordinates
    have hpoint : ∀ X' : {j : V // j ≠ v₀} → β,
        ∑ y, (∏ v ∈ Finset.univ.filter (fun v : V => v ≠ r),
            I (e.symm (y, X') (p v)) (e.symm (y, X') v)
              * w (e.symm (y, X') v)) * w (e.symm (y, X') r)
        ≤ ((∏ v' ∈ Finset.univ.filter
              (fun v : {j : V // j ≠ v₀} => v ≠ r'),
            I (X' (p' v')) (X' v') * w (X' v')) * w (X' r')) * A := by
      intro X'
      have hterm : ∀ y : β,
          (∏ v ∈ Finset.univ.filter (fun v : V => v ≠ r),
              I (e.symm (y, X') (p v)) (e.symm (y, X') v)
                * w (e.symm (y, X') v)) * w (e.symm (y, X') r)
          = (I (X' ⟨p v₀, hpv₀⟩) y * w y) *
            ((∏ v' ∈ Finset.univ.filter
                (fun v : {j : V // j ≠ v₀} => v ≠ r'),
              I (X' (p' v')) (X' v') * w (X' v')) * w (X' r')) := by
        intro y
        rw [← Finset.mul_prod_erase _ _ hv₀mem, heval₀,
          hevalne y X' (p v₀) hpv₀, hevalne y X' r hrv₀]
        have hprod : (∏ v ∈ (Finset.univ.filter
              (fun v : V => v ≠ r)).erase v₀,
            I (e.symm (y, X') (p v)) (e.symm (y, X') v)
              * w (e.symm (y, X') v))
            = ∏ v' ∈ Finset.univ.filter
                (fun v : {j : V // j ≠ v₀} => v ≠ r'),
              I (X' (p' v')) (X' v') * w (X' v') := by
          refine Finset.prod_bij'
            (fun v hv => (⟨v, (Finset.mem_erase.mp hv).1⟩ : {j : V // j ≠ v₀}))
            (fun v' _ => v'.1) ?_ ?_ ?_ ?_ ?_
          · intro v hv
            have hvr : v ≠ r :=
              (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, fun hEq => hvr (congrArg Subtype.val hEq)⟩
          · intro v' hv'
            have hv'r : v'.1 ≠ r := by
              intro h
              have : v' = r' := Subtype.ext h
              rw [Finset.mem_filter] at hv'
              exact hv'.2 this
            rw [Finset.mem_erase]
            exact ⟨v'.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'r⟩⟩
          · intro v hv
            rfl
          · intro v' hv'
            rfl
          · intro v hv
            have hvne : v ≠ v₀ := (Finset.mem_erase.mp hv).1
            have hvr : v ≠ r :=
              (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2
            have hpne : p v ≠ v₀ := hleaf v hvr
            have hpeq : p' ⟨v, hvne⟩ = ⟨p v, hpne⟩ := by
              simp only [hp'def]
              rw [dif_neg hpne]
            rw [hevalne y X' v hvne, hevalne y X' (p v) hpne, hpeq]
        rw [hprod]
        ring
      have hD0 : 0 ≤ (∏ v' ∈ Finset.univ.filter
            (fun v : {j : V // j ≠ v₀} => v ≠ r'),
          I (X' (p' v')) (X' v') * w (X' v')) * w (X' r') :=
        mul_nonneg (Finset.prod_nonneg fun v' _ =>
          mul_nonneg (hI _ _) (hw _)) (hw _)
      calc ∑ y, (∏ v ∈ Finset.univ.filter (fun v : V => v ≠ r),
              I (e.symm (y, X') (p v)) (e.symm (y, X') v)
                * w (e.symm (y, X') v)) * w (e.symm (y, X') r)
          = ∑ y, (I (X' ⟨p v₀, hpv₀⟩) y * w y) *
              ((∏ v' ∈ Finset.univ.filter
                  (fun v : {j : V // j ≠ v₀} => v ≠ r'),
                I (X' (p' v')) (X' v') * w (X' v')) * w (X' r')) :=
            Finset.sum_congr rfl fun y _ => hterm y
        _ = (∑ y, I (X' ⟨p v₀, hpv₀⟩) y * w y) *
              ((∏ v' ∈ Finset.univ.filter
                  (fun v : {j : V // j ≠ v₀} => v ≠ r'),
                I (X' (p' v')) (X' v') * w (X' v')) * w (X' r')) := by
            rw [← Finset.sum_mul]
        _ ≤ A * ((∏ v' ∈ Finset.univ.filter
                  (fun v : {j : V // j ≠ v₀} => v ≠ r'),
                I (X' (p' v')) (X' v') * w (X' v')) * w (X' r')) :=
            mul_le_mul_of_nonneg_right (hsum _) hD0
        _ = ((∏ v' ∈ Finset.univ.filter
                  (fun v : {j : V // j ≠ v₀} => v ≠ r'),
                I (X' (p' v')) (X' v') * w (X' v')) * w (X' r')) * A :=
            mul_comm _ _
    calc ∑ X' : {j : V // j ≠ v₀} → β, ∑ y,
          (∏ v ∈ Finset.univ.filter (fun v : V => v ≠ r),
            I (e.symm (y, X') (p v)) (e.symm (y, X') v)
              * w (e.symm (y, X') v)) * w (e.symm (y, X') r)
        ≤ ∑ X' : {j : V // j ≠ v₀} → β,
            ((∏ v' ∈ Finset.univ.filter
                (fun v : {j : V // j ≠ v₀} => v ≠ r'),
              I (X' (p' v')) (X' v') * w (X' v')) * w (X' r')) * A :=
          Finset.sum_le_sum fun X' _ => hpoint X'
      _ = (∑ X' : {j : V // j ≠ v₀} → β,
            (∏ v' ∈ Finset.univ.filter
                (fun v : {j : V // j ≠ v₀} => v ≠ r'),
              I (X' (p' v')) (X' v') * w (X' v')) * w (X' r')) * A := by
          rw [← Finset.sum_mul]
      _ ≤ (A ^ n * ∑ y, w y) * A := by
          refine mul_le_mul_of_nonneg_right ?_ hA
          exact ih _ β r' p' (fun v => lev v.1) I w A hcard' hdesc'
            hI hw hA hsum
      _ = A ^ (n + 1) * ∑ y, w y := by ring

/-- **Vertexwise tree-walk bound.**  This is the same leaf-removal walk as
`tree_walk_bound`, but the kernel and one-step budget may depend on the child
vertex.  It is the finite bookkeeping form needed by degree-sensitive
leaf-summation arguments: each removed nonroot vertex pays its own `A v`, and
the root is summed only once through `wroot`. -/
theorem tree_walk_bound_vertexwise (n : ℕ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (β : Type*) [Fintype β]
      (r : V) (p : V → V) (lev : V → ℕ)
      (I : V → β → β → ℝ) (wroot : β → ℝ) (A : V → ℝ),
      Fintype.card V = n + 1 →
      (∀ v, v ≠ r → lev (p v) < lev v) →
      (∀ v x y, 0 ≤ I v x y) → (∀ y, 0 ≤ wroot y) →
      (∀ v, v ≠ r → 0 ≤ A v) →
      (∀ v, v ≠ r → ∀ x : β, ∑ y, I v x y ≤ A v) →
      ∑ X : V → β,
        (∏ v ∈ Finset.univ.filter (fun v => v ≠ r),
          I v (X (p v)) (X v)) * wroot (X r)
        ≤
      (∏ v ∈ Finset.univ.filter (fun v => v ≠ r), A v) *
        ∑ y, wroot y := by
  induction n with
  | zero =>
    intro V _ _ β _ r p lev I wroot A hcard hdesc hI hwroot hA hsum
    have hsub : Subsingleton V :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hfil : Finset.univ.filter (fun v : V => v ≠ r) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v _
      simp [Subsingleton.elim v r]
    rw [hfil]
    simp only [Finset.prod_empty, one_mul]
    refine le_of_eq (Fintype.sum_bijective (fun X : V → β => X r)
      ⟨?_, ?_⟩ _ _ (fun X => rfl))
    · intro X Y h
      funext v
      rw [Subsingleton.elim v r]
      exact h
    · intro y
      exact ⟨fun _ => y, rfl⟩
  | succ n ih =>
    intro V _ _ β _ r p lev I wroot A hcard hdesc hI hwroot hA hsum
    classical
    -- Choose a nonroot vertex of maximal level; the descent hypothesis makes it
    -- a leaf, so its coordinate appears in exactly one edge factor.
    have hne : (Finset.univ.filter (fun v : V => v ≠ r)).Nonempty := by
      have h1 : 1 < Fintype.card V := by omega
      obtain ⟨v, hv⟩ := Fintype.exists_ne_of_one_lt_card h1 r
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
    obtain ⟨v₀, hv₀mem, hv₀max⟩ :=
      Finset.exists_max_image (Finset.univ.filter (fun v : V => v ≠ r)) lev hne
    have hv₀r : v₀ ≠ r := (Finset.mem_filter.mp hv₀mem).2
    have hleaf : ∀ v : V, v ≠ r → p v ≠ v₀ := by
      intro v hvr hpv
      have h1 := hdesc v hvr
      rw [hpv] at h1
      have h2 := hv₀max v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvr⟩)
      omega
    have hpv₀ : p v₀ ≠ v₀ := by
      intro h
      have h1 := hdesc v₀ hv₀r
      rw [h] at h1
      omega
    have hrv₀ : r ≠ v₀ := Ne.symm hv₀r
    have hcard' : Fintype.card {j : V // j ≠ v₀} = n + 1 := by
      rw [Fintype.card_subtype, Finset.filter_ne',
        Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ]
      omega
    set r' : {j : V // j ≠ v₀} := ⟨r, hrv₀⟩ with hr'def
    set p' : {j : V // j ≠ v₀} → {j : V // j ≠ v₀} :=
      fun v => if h : p v.1 = v₀ then r' else ⟨p v.1, h⟩ with hp'def
    have hdesc' : ∀ v : {j : V // j ≠ v₀}, v ≠ r' →
        lev (p' v).1 < lev v.1 := by
      intro v hvr'
      have hv1r : v.1 ≠ r := by
        intro h
        exact hvr' (Subtype.ext h)
      have hpne : p v.1 ≠ v₀ := hleaf v.1 hv1r
      have hpeq : p' v = ⟨p v.1, hpne⟩ := by
        simp only [hp'def]
        rw [dif_neg hpne]
      rw [hpeq]
      exact hdesc v.1 hv1r
    have hAprod :
        (∏ v' ∈ Finset.univ.filter
            (fun v : {j : V // j ≠ v₀} => v ≠ r'), A v'.1)
          =
        ∏ v ∈ (Finset.univ.filter (fun v : V => v ≠ r)).erase v₀, A v := by
      refine Finset.prod_bij'
        (fun v' _ => v'.1)
        (fun v hv => (⟨v, (Finset.mem_erase.mp hv).1⟩ : {j : V // j ≠ v₀}))
        ?_ ?_ ?_ ?_ ?_
      · intro v' hv'
        have hv'r : v'.1 ≠ r := by
          intro h
          have : v' = r' := Subtype.ext h
          rw [Finset.mem_filter] at hv'
          exact hv'.2 this
        rw [Finset.mem_erase]
        exact ⟨v'.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'r⟩⟩
      · intro v hv
        have hvr : v ≠ r :=
          (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, fun hEq => hvr (congrArg Subtype.val hEq)⟩
      · intro v' hv'
        rfl
      · intro v hv
        rfl
      · intro v' hv'
        rfl
    set e := Equiv.funSplitAt v₀ β with hedef
    have heval₀ : ∀ (y : β) (X' : {j : V // j ≠ v₀} → β),
        e.symm (y, X') v₀ = y := by
      intro y X'
      simp [hedef]
    have hevalne : ∀ (y : β) (X' : {j : V // j ≠ v₀} → β) (j : V)
        (hj : j ≠ v₀), e.symm (y, X') j = X' ⟨j, hj⟩ := by
      intro y X' j hj
      simp [hedef, hj]
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
    have hpoint : ∀ X' : {j : V // j ≠ v₀} → β,
        ∑ y, (∏ v ∈ Finset.univ.filter (fun v : V => v ≠ r),
            I v (e.symm (y, X') (p v)) (e.symm (y, X') v)) *
              wroot (e.symm (y, X') r)
        ≤
        ((∏ v' ∈ Finset.univ.filter
              (fun v : {j : V // j ≠ v₀} => v ≠ r'),
            I v'.1 (X' (p' v')) (X' v')) * wroot (X' r')) * A v₀ := by
      intro X'
      have hterm : ∀ y : β,
          (∏ v ∈ Finset.univ.filter (fun v : V => v ≠ r),
              I v (e.symm (y, X') (p v)) (e.symm (y, X') v)) *
                wroot (e.symm (y, X') r)
          =
          I v₀ (X' ⟨p v₀, hpv₀⟩) y *
            ((∏ v' ∈ Finset.univ.filter
                (fun v : {j : V // j ≠ v₀} => v ≠ r'),
              I v'.1 (X' (p' v')) (X' v')) * wroot (X' r')) := by
        intro y
        rw [← Finset.mul_prod_erase _ _ hv₀mem, heval₀,
          hevalne y X' (p v₀) hpv₀, hevalne y X' r hrv₀]
        have hprod : (∏ v ∈ (Finset.univ.filter
              (fun v : V => v ≠ r)).erase v₀,
            I v (e.symm (y, X') (p v)) (e.symm (y, X') v))
            =
            ∏ v' ∈ Finset.univ.filter
                (fun v : {j : V // j ≠ v₀} => v ≠ r'),
              I v'.1 (X' (p' v')) (X' v') := by
          refine Finset.prod_bij'
            (fun v hv => (⟨v, (Finset.mem_erase.mp hv).1⟩ : {j : V // j ≠ v₀}))
            (fun v' _ => v'.1) ?_ ?_ ?_ ?_ ?_
          · intro v hv
            have hvr : v ≠ r :=
              (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, fun hEq => hvr (congrArg Subtype.val hEq)⟩
          · intro v' hv'
            have hv'r : v'.1 ≠ r := by
              intro h
              have : v' = r' := Subtype.ext h
              rw [Finset.mem_filter] at hv'
              exact hv'.2 this
            rw [Finset.mem_erase]
            exact ⟨v'.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'r⟩⟩
          · intro v hv
            rfl
          · intro v' hv'
            rfl
          · intro v hv
            have hvne : v ≠ v₀ := (Finset.mem_erase.mp hv).1
            have hvr : v ≠ r :=
              (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2
            have hpne : p v ≠ v₀ := hleaf v hvr
            have hpeq : p' ⟨v, hvne⟩ = ⟨p v, hpne⟩ := by
              simp only [hp'def]
              rw [dif_neg hpne]
            rw [hevalne y X' v hvne, hevalne y X' (p v) hpne, hpeq]
        rw [hprod]
        ring
      have hD0 : 0 ≤ (∏ v' ∈ Finset.univ.filter
            (fun v : {j : V // j ≠ v₀} => v ≠ r'),
          I v'.1 (X' (p' v')) (X' v')) * wroot (X' r') :=
        mul_nonneg (Finset.prod_nonneg fun v' _ => hI v'.1 _ _) (hwroot _)
      calc ∑ y, (∏ v ∈ Finset.univ.filter (fun v : V => v ≠ r),
              I v (e.symm (y, X') (p v)) (e.symm (y, X') v)) *
                wroot (e.symm (y, X') r)
          =
          ∑ y, I v₀ (X' ⟨p v₀, hpv₀⟩) y *
            ((∏ v' ∈ Finset.univ.filter
                (fun v : {j : V // j ≠ v₀} => v ≠ r'),
              I v'.1 (X' (p' v')) (X' v')) * wroot (X' r')) := by
            exact Finset.sum_congr rfl fun y _ => hterm y
        _ =
          (∑ y, I v₀ (X' ⟨p v₀, hpv₀⟩) y) *
            ((∏ v' ∈ Finset.univ.filter
                (fun v : {j : V // j ≠ v₀} => v ≠ r'),
              I v'.1 (X' (p' v')) (X' v')) * wroot (X' r')) := by
            rw [← Finset.sum_mul]
        _ ≤
          A v₀ *
            ((∏ v' ∈ Finset.univ.filter
                (fun v : {j : V // j ≠ v₀} => v ≠ r'),
              I v'.1 (X' (p' v')) (X' v')) * wroot (X' r')) :=
            mul_le_mul_of_nonneg_right
              (hsum v₀ hv₀r (X' ⟨p v₀, hpv₀⟩)) hD0
        _ =
          ((∏ v' ∈ Finset.univ.filter
              (fun v : {j : V // j ≠ v₀} => v ≠ r'),
            I v'.1 (X' (p' v')) (X' v')) * wroot (X' r')) * A v₀ := by
            ring
    calc ∑ X' : {j : V // j ≠ v₀} → β, ∑ y,
          (∏ v ∈ Finset.univ.filter (fun v : V => v ≠ r),
            I v (e.symm (y, X') (p v)) (e.symm (y, X') v)) *
              wroot (e.symm (y, X') r)
        ≤
        ∑ X' : {j : V // j ≠ v₀} → β,
          ((∏ v' ∈ Finset.univ.filter
              (fun v : {j : V // j ≠ v₀} => v ≠ r'),
            I v'.1 (X' (p' v')) (X' v')) * wroot (X' r')) * A v₀ :=
          Finset.sum_le_sum fun X' _ => hpoint X'
      _ =
        (∑ X' : {j : V // j ≠ v₀} → β,
          (∏ v' ∈ Finset.univ.filter
              (fun v : {j : V // j ≠ v₀} => v ≠ r'),
            I v'.1 (X' (p' v')) (X' v')) * wroot (X' r')) * A v₀ := by
          rw [← Finset.sum_mul]
      _ ≤
        (((∏ v' ∈ Finset.univ.filter
              (fun v : {j : V // j ≠ v₀} => v ≠ r'), A v'.1) *
            ∑ y, wroot y) * A v₀) := by
          refine mul_le_mul_of_nonneg_right ?_ (hA v₀ hv₀r)
          exact ih _ β r' p' (fun v => lev v.1)
            (fun v x y => I v.1 x y) wroot (fun v => A v.1)
            hcard' hdesc'
            (fun v x y => hI v.1 x y)
            hwroot
            (fun v hv => by
              have hv1r : v.1 ≠ r := by
                intro h
                exact hv (Subtype.ext h)
              exact hA v.1 hv1r)
            (fun v hv x => by
              have hv1r : v.1 ≠ r := by
                intro h
                exact hv (Subtype.ext h)
              exact hsum v.1 hv1r x)
      _ =
        (∏ v ∈ Finset.univ.filter (fun v : V => v ≠ r), A v) *
          ∑ y, wroot y := by
          rw [← Finset.mul_prod_erase _ _ hv₀mem, ← hAprod]
          ring

end YangMills.KP
