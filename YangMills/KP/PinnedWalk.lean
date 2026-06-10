/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.WalkBound

/-!
# Sharp KP, step 2 — the pinned tree-walk bound

`docs/SHARP-KP-PLAN.md` §5, first brick.  The original `tree_walk_bound`
sums over a *free* root value and pays the extensive factor `∑ w`; the sharp
campaign needs the **root fiber**:

  `∑_{X : X r = x₀} ∏_{v ≠ r} I(X_{p v}, X_v)·w(X_v) ≤ Aⁿ`.

Rather than re-running the leaf-removal induction, we *derive* the pinned
bound from the free one by a marker construction: extend the value type to
`Option β`, where `none` is a synthetic root value of weight `T` that
interacts like `x₀` (`I'(none, some y) = I(x₀, y)`) and can never occur at a
non-root vertex (`I'(·, none) = 0`).  The free bound then gives
`T·(pinned sum) ≤ Aⁿ·(T + ∑w)` for **every** `T ≥ 0`, and instantiating a
single sufficiently large `T` forces `pinned sum ≤ Aⁿ` — no limits needed.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

/-- **The pinned tree-walk bound:** the root fiber of the tree-structured
assignment sum is bounded by `Aⁿ` alone — no `∑ w` factor, no dependence on
the size of the value space.  This is the volume-free form the sharp KP
estimate consumes. -/
theorem tree_walk_bound_pinned (n : ℕ)
    (V : Type) [Fintype V] [DecidableEq V] (β : Type*) [Fintype β]
    [DecidableEq β]
    (r : V) (p : V → V) (lev : V → ℕ)
    (I : β → β → ℝ) (w : β → ℝ) (A : ℝ)
    (hcard : Fintype.card V = n + 1)
    (hdesc : ∀ v, v ≠ r → lev (p v) < lev v)
    (hI : ∀ x y, 0 ≤ I x y) (hw : ∀ y, 0 ≤ w y) (hA : 0 ≤ A)
    (hsum : ∀ x : β, ∑ y, I x y * w y ≤ A) (x₀ : β) :
    ∑ X ∈ (Finset.univ : Finset (V → β)).filter (fun X => X r = x₀),
      ∏ v ∈ Finset.univ.filter (fun v => v ≠ r),
        I (X (p v)) (X v) * w (X v)
      ≤ A ^ n := by
  classical
  set P : ℝ := ∑ X ∈ (Finset.univ : Finset (V → β)).filter
    (fun X => X r = x₀),
    ∏ v ∈ Finset.univ.filter (fun v => v ≠ r),
      I (X (p v)) (X v) * w (X v) with hPdef
  -- Main estimate: for every nonnegative synthetic root weight `T`,
  -- `T·P ≤ Aⁿ·(T + ∑ w)`.
  have hmain : ∀ T : ℝ, 0 ≤ T → T * P ≤ A ^ n * (T + ∑ y, w y) := by
    intro T hT
    -- the marker system on `Option β`, abbreviated
    set F : (V → Option β) → ℝ := fun X' =>
      (∏ v ∈ Finset.univ.filter (fun v => v ≠ r),
        (X' v).elim 0 (fun y => (X' (p v)).elim (I x₀ y) (fun x => I x y))
          * (X' v).elim T w) * (X' r).elim T w with hFdef
    set e : (V → β) → (V → Option β) :=
      fun X u => if u = r then none else some (X u) with hedef
    have hFnn : ∀ X', 0 ≤ F X' := by
      intro X'
      rw [hFdef]
      refine mul_nonneg (Finset.prod_nonneg fun v _ =>
        mul_nonneg ?_ ?_) ?_
      · cases hb : X' v with
        | none => simp
        | some y =>
            cases ha : X' (p v) with
            | none => simpa using hI x₀ y
            | some x => simpa using hI x y
      · cases hb : X' v with
        | none => simpa using hT
        | some y => simpa using hw y
      · cases hb : X' r with
        | none => simpa using hT
        | some y => simpa using hw y
    -- the free walk bound on the marker system
    have key := tree_walk_bound n V (Option β) r p lev
      (fun a b => b.elim 0 (fun y => a.elim (I x₀ y) (fun x => I x y)))
      (fun a => a.elim T w) A hcard hdesc
      (by
        intro a b
        cases b with
        | none => simp
        | some y =>
            cases a with
            | none => simpa using hI x₀ y
            | some x => simpa using hI x y)
      (by
        intro a
        cases a with
        | none => simpa using hT
        | some y => simpa using hw y)
      hA
      (by
        intro x'
        rw [Fintype.sum_option]
        cases x' with
        | none => simpa using hsum x₀
        | some x => simpa using hsum x)
    rw [Fintype.sum_option] at key
    simp only [Option.elim_none, Option.elim_some, zero_mul, zero_add] at key
    have key' : ∑ X' : V → Option β, F X' ≤ A ^ n * (T + ∑ y, w y) := by
      refine le_trans (le_of_eq ?_) key
      rw [hFdef]
    -- pinned configurations embed into the marker system with weight `T`
    have hval : ∀ X ∈ (Finset.univ : Finset (V → β)).filter
        (fun X => X r = x₀),
        T * ∏ v ∈ Finset.univ.filter (fun v => v ≠ r),
          I (X (p v)) (X v) * w (X v) = F (e X) := by
      intro X hX
      rw [Finset.mem_filter] at hX
      have hXr : X r = x₀ := hX.2
      rw [hFdef, hedef]
      beta_reduce
      rw [if_pos rfl]
      simp only [Option.elim_none]
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun v hv => ?_
      have hvr : v ≠ r := (Finset.mem_filter.mp hv).2
      rw [if_neg hvr]
      simp only [Option.elim_some]
      by_cases hp : p v = r
      · rw [if_pos hp]
        simp only [Option.elim_none]
        rw [hp, hXr]
      · rw [if_neg hp]
        simp only [Option.elim_some]
    have hinj : ∀ X ∈ (Finset.univ : Finset (V → β)).filter
        (fun X => X r = x₀),
        ∀ Y ∈ (Finset.univ : Finset (V → β)).filter
          (fun X => X r = x₀), e X = e Y → X = Y := by
      intro X hX Y hY h
      rw [Finset.mem_filter] at hX hY
      funext v
      by_cases hv : v = r
      · rw [hv, hX.2, hY.2]
      · have hcf := congrFun h v
        rw [hedef] at hcf
        beta_reduce at hcf
        rw [if_neg hv, if_neg hv] at hcf
        exact Option.some.inj hcf
    calc T * P
        = ∑ X ∈ (Finset.univ : Finset (V → β)).filter
            (fun X => X r = x₀),
            T * ∏ v ∈ Finset.univ.filter (fun v => v ≠ r),
              I (X (p v)) (X v) * w (X v) := by
          rw [hPdef, Finset.mul_sum]
      _ = ∑ X ∈ (Finset.univ : Finset (V → β)).filter
            (fun X => X r = x₀), F (e X) :=
          Finset.sum_congr rfl hval
      _ = ∑ X' ∈ ((Finset.univ : Finset (V → β)).filter
            (fun X => X r = x₀)).image e, F X' :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ X' : V → Option β, F X' :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun X' _ _ => hFnn X')
      _ ≤ A ^ n * (T + ∑ y, w y) := key'
  -- A single large `T` forces the conclusion.
  by_contra hgt
  push_neg at hgt
  have hWnn : (0 : ℝ) ≤ A ^ n * ∑ y, w y :=
    mul_nonneg (pow_nonneg hA n) (Finset.sum_nonneg fun y _ => hw y)
  set T₀ : ℝ := (A ^ n * ∑ y, w y + 1) / (P - A ^ n) with hT₀def
  have hDpos : (0 : ℝ) < P - A ^ n := by linarith
  have hT₀nn : 0 ≤ T₀ := div_nonneg (by linarith) hDpos.le
  have h1 := hmain T₀ hT₀nn
  have h2 : T₀ * (P - A ^ n) = A ^ n * ∑ y, w y + 1 := by
    rw [hT₀def, div_mul_cancel₀]
    exact hDpos.ne'
  nlinarith [h1, h2]

end YangMills.KP
