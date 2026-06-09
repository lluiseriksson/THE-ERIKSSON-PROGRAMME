# Step (ii) — the per-tree activity walk: exact statement + mechanical proof plan

**Status:** OPEN (last open step of `kp_per_size_bound`).  All inputs proved
(`prod_tree_eq_prod_parents`, `maxLevel_not_parent`, `kp_neighbor_sum_le`).
This file is the execution plan for one focused session.

## The abstract lemma to prove (new file `YangMills/KP/WalkBound.lean`)

Abstract over the vertex type so leaf removal is plain induction on `n`
(no `Fin`-reindexing):

```lean
theorem tree_walk_bound :
    ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V]
      (β : Type) [Fintype β]
      (r : V) (p : V → V) (lev : V → ℕ)
      (I : β → β → ℝ) (w : β → ℝ) (A : ℝ),
      Fintype.card V = n + 1 →
      (∀ v, v ≠ r → lev (p v) < lev v) →          -- parent map descends
      (∀ x y, 0 ≤ I x y) → (∀ y, 0 ≤ w y) → 0 ≤ A →
      (∀ x, ∑ y, I x y * w y ≤ A) →               -- the KP neighbour bound
      ∑ X : V → β,
        (∏ v ∈ Finset.univ.filter (· ≠ r), I (X (p v)) (X v) * w (X v))
          * w (X r)
        ≤ A ^ n * ∑ y, w y
```

Instantiation: `V := Fin (m+1)`, `r := 0`, `p := bfsParent T`,
`lev := bfsLevel T`, `β := P.Polymer`, `w := ‖P.activity ·‖`,
`I x y := if P.incomp x y then 1 else 0`, `A := max of a` —
the hypothesis `∑ y, I x y * w y ≤ A` is `kp_neighbor_sum_le` + `a ≤ A`.
The tree-indicator product converts to this parent-indexed form by
`prod_tree_eq_prod_parents`; descent is `bfsParent_spec`.

## Proof plan (plain induction on `n`, `V` universally quantified inside)

**Base `n = 0`:** `card V = 1` ⇒ `Subsingleton V`
(`Fintype.card_le_one_iff_subsingleton`); the filter `(· ≠ r)` is empty
(`Finset.filter_eq_empty_iff`, `Subsingleton.elim`); `∏ = 1`;
`∑ X, w (X r) = ∑ y, w y` by the bijection `X ↦ X r`
(`Fintype.sum_bijective`; injective by `funext` + `Subsingleton`, surjective
by constants).  Finish `pow_zero, one_mul, le_of_eq`.

**Step:** `card V = n + 2`.
1. Pick `v₀` maximizing `lev` on `univ.filter (· ≠ r)`
   (`Finset.exists_max_image`; nonempty by `Fintype.exists_ne r` since
   `1 < card V`).
2. Leaf property: `∀ v ≠ r, p v ≠ v₀` (descent + maximality — the
   `maxLevel_not_parent` argument, here one `omega`).
3. Split the function space at `v₀`:
   `Equiv.piSplitAt v₀ (fun _ => β) : (V → β) ≃ β × ({j // j ≠ v₀} → β)`;
   transport the sum (`Fintype.sum_equiv`), then `Fintype.sum_prod_type`.
   Clean the `dite`s from `Equiv.piSplitAt_symm_apply` with
   `dif_pos rfl` / `dif_neg`.
4. Split off the `v₀` factor (`Finset.mul_prod_erase` with
   `v₀ ∈ filter`); by the leaf property every remaining factor reads only
   coordinates `≠ v₀`, and `p v₀ ≠ v₀` (descent), so the inner `∑ y` is
   `∑ y, I (X' ⟨p v₀, _⟩) y * w y ≤ A`.
5. Apply the induction hypothesis on `V' := {j // j ≠ v₀}`
   (`Fintype.card_subtype_ne`-style: `card V' = n + 1`), with
   `r' := ⟨r, (Finset.mem_filter.mp hv₀).2.symm…⟩` (note `v₀ ≠ r`),
   `p' := fun v => if h : p v.1 = v₀ then r' else ⟨p v.1, h⟩`
   (the `if` is never taken for `v ≠ r'`, by the leaf property — resolve
   with `dif_neg`), `lev' := lev ∘ Subtype.val`.
   Reindex the remaining product to subtype indices with `Finset.prod_bij`
   (`v ↦ ⟨v, hv⟩` between `(univ.filter (· ≠ r)).erase v₀` and
   `univ.filter (· ≠ r')`).
6. Assemble: `S ≤ A * (Aⁿ * ∑ w) = A^(n+1) * ∑ w` (`pow_succ`, `ring_nf`,
   nonnegativity side conditions by `positivity` / `Finset.sum_nonneg` /
   `Finset.prod_nonneg`).

## What it unlocks (assembly, step after)

`kp_per_size_bound`:
`clusterWeight P n ≤ (1/(n+1)!)·treeCount(n+1)·(walk bound)`
with `abs_ursell_le_treeCount` → counting swap (`Finset.sum_comm`),
`treeCount_le_pow`, `succ_pow_le_exp_mul_factorial` ⇒
`clusterWeight P n ≤ (∑‖z‖)·(e·A)ⁿ` — geometric for `e·A < 1`.
Feed `clusterSum_summable_of_geometric` / `norm_clusterSum_le`:
**KP convergence, Target B closed.**  (This uses uniform smallness
`A := max a` with `e·A < 1` — sufficient for M3-grade results; honest note:
slightly stronger than the sharp KP criterion, which can be refined later
without touching the architecture.)

All of this is **M3 lattice-side**; none of it affects M4/M5/Clay
(`docs/DEPENDENCY-GRAPH.md` §2).
