/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Finite multiaffine interpolation

This module gives a list-ordered vertex interpolation for functions on a
finite real coordinate space.  The interpolant is a finite polynomial, hence
smooth to every order.  A source-independent theorem proves that it agrees
exactly with any function which is affine in each listed coordinate.

The construction is used below to replace a convergent random-walk
representation by a finite polynomial on the physical weakening cube; it does
not assume any analytic regularity of the original function.
-/

namespace YangMills.RG

noncomputable section

/-- Replace the coordinates listed in `L` by their values in `u`, retaining
the coordinates of `base` outside `L`. -/
def cmp116AssignWeakeningList
    {D : Type*} [DecidableEq D]
    (base u : D → ℝ) (L : List D) : D → ℝ :=
  fun d => if d ∈ L then u d else base d

@[simp] theorem cmp116AssignWeakeningList_nil
    {D : Type*} [DecidableEq D]
    (base u : D → ℝ) :
    cmp116AssignWeakeningList base u [] = base := by
  funext d
  simp [cmp116AssignWeakeningList]

theorem cmp116AssignWeakeningList_cons_of_not_mem
    {D : Type*} [DecidableEq D]
    (base u : D → ℝ) (d : D) (L : List D) :
    cmp116AssignWeakeningList base u (d :: L) =
      Function.update (cmp116AssignWeakeningList base u L) d (u d) := by
  funext x
  by_cases hxd : x = d
  · subst x
    simp [cmp116AssignWeakeningList]
  · simp [cmp116AssignWeakeningList, hxd]

theorem cmp116AssignWeakeningList_update_base_of_not_mem
    {D : Type*} [DecidableEq D]
    (base u : D → ℝ) (d : D) (L : List D) (z : ℝ)
    (hdL : d ∉ L) :
    cmp116AssignWeakeningList (Function.update base d z) u L =
      Function.update (cmp116AssignWeakeningList base u L) d z := by
  funext x
  by_cases hxL : x ∈ L
  · have hxd : x ≠ d := by
      intro h
      subst x
      exact hdL hxL
    simp [cmp116AssignWeakeningList, hxL, hxd]
  · by_cases hxd : x = d
    · subst x
      simp [cmp116AssignWeakeningList, hdL]
    · simp [cmp116AssignWeakeningList, hxL, hxd]

/-- List-ordered finite vertex interpolation.  The `base` argument is fixed
at construction time, so every leaf is a constant and the result is a genuine
finite polynomial in `u`. -/
noncomputable def cmp116FiniteMultiaffineInterpolation
    {D E : Type*}
    [DecidableEq D]
    [AddCommGroup E] [Module ℝ E]
    (f : (D → ℝ) → E) :
    (base : D → ℝ) → List D → (D → ℝ) → E
  | base, [] => fun _ => f base
  | base, d :: L => fun u =>
      (1 - u d) •
          cmp116FiniteMultiaffineInterpolation f
            (Function.update base d 0) L u +
        u d •
          cmp116FiniteMultiaffineInterpolation f
            (Function.update base d 1) L u

/-- The finite vertex interpolant is smooth to every requested order,
independently of any regularity of the sampled function `f`. -/
theorem contDiff_cmp116FiniteMultiaffineInterpolation
    {D E : Type*}
    [Fintype D] [DecidableEq D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : WithTop ℕ∞)
    (f : (D → ℝ) → E) (base : D → ℝ) (L : List D) :
    ContDiff ℝ n (cmp116FiniteMultiaffineInterpolation f base L) := by
  induction L generalizing base with
  | nil =>
      simpa [cmp116FiniteMultiaffineInterpolation] using
        (contDiff_const : ContDiff ℝ n (fun _ : D → ℝ => f base))
  | cons d L ih =>
      have hcoord :
          ContDiff ℝ n (fun u : D → ℝ => u d) :=
        contDiff_apply (n := n) ℝ ℝ d
      simpa [cmp116FiniteMultiaffineInterpolation] using
        ((contDiff_const.sub hcoord).smul
          (ih (Function.update base d 0))).add
        (hcoord.smul (ih (Function.update base d 1)))

/-- Exact interpolation of a function affine in every selected coordinate. -/
theorem cmp116FiniteMultiaffineInterpolation_eq_of_coordinateAffine
    {D E : Type*}
    [DecidableEq D]
    [AddCommGroup E] [Module ℝ E]
    (f : (D → ℝ) → E)
    (base u : D → ℝ) (L : List D) (hL : L.Nodup)
    (haffine : ∀ (x : D → ℝ) (d : D) (t : ℝ),
      f (Function.update x d t) =
        (1 - t) • f (Function.update x d 0) +
          t • f (Function.update x d 1)) :
    cmp116FiniteMultiaffineInterpolation f base L u =
      f (cmp116AssignWeakeningList base u L) := by
  induction L generalizing base with
  | nil =>
      simp [cmp116FiniteMultiaffineInterpolation]
  | cons d L ih =>
      have hdL : d ∉ L := (List.nodup_cons.mp hL).1
      have hLNodup : L.Nodup := (List.nodup_cons.mp hL).2
      change
        (1 - u d) •
            cmp116FiniteMultiaffineInterpolation f
              (Function.update base d 0) L u +
          u d •
            cmp116FiniteMultiaffineInterpolation f
              (Function.update base d 1) L u =
        f (cmp116AssignWeakeningList base u (d :: L))
      rw [ih (Function.update base d 0) hLNodup,
        ih (Function.update base d 1) hLNodup]
      rw [cmp116AssignWeakeningList_update_base_of_not_mem
          base u d L 0 hdL,
        cmp116AssignWeakeningList_update_base_of_not_mem
          base u d L 1 hdL,
        cmp116AssignWeakeningList_cons_of_not_mem base u d L]
      exact
        (haffine (cmp116AssignWeakeningList base u L) d (u d)).symm

/-- If the coordinate list covers the finite coordinate type, assignment
through that list recovers the supplied point exactly. -/
theorem cmp116AssignWeakeningList_eq_of_forall_mem
    {D : Type*} [DecidableEq D]
    (base u : D → ℝ) (L : List D)
    (hcover : ∀ d : D, d ∈ L) :
    cmp116AssignWeakeningList base u L = u := by
  funext d
  simp [cmp116AssignWeakeningList, hcover d]

/-- A globally separately affine function on a finite coordinate space is
equal to a finite smooth polynomial. -/
theorem contDiff_of_coordinateAffine
    {D E : Type*}
    [Fintype D] [DecidableEq D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : WithTop ℕ∞)
    (f : (D → ℝ) → E)
    (L : List D) (hL : L.Nodup)
    (hcover : ∀ d : D, d ∈ L)
    (haffine : ∀ (x : D → ℝ) (d : D) (t : ℝ),
      f (Function.update x d t) =
        (1 - t) • f (Function.update x d 0) +
          t • f (Function.update x d 1)) :
    ContDiff ℝ n f := by
  let base : D → ℝ := fun _ => 0
  have heq :
      cmp116FiniteMultiaffineInterpolation f base L = f := by
    funext u
    rw [cmp116FiniteMultiaffineInterpolation_eq_of_coordinateAffine
      f base u L hL haffine]
    rw [cmp116AssignWeakeningList_eq_of_forall_mem base u L hcover]
  rw [← heq]
  exact contDiff_cmp116FiniteMultiaffineInterpolation n f base L

end

end YangMills.RG
