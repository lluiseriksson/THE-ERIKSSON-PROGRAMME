/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinLattice
import YangMills.OS.DobrushinVolumeEquiv

/-!
# D-7 — two centred Ising rectangles

The smaller `(2n+1) × (2n+1)` rectangle is placed at the centre of the larger
`(2m+1) × (2m+1)` rectangle.  Its active subtype is explicitly equivalent to
the smaller rectangle, and the pulled-back active coupling is definitionally
the same nearest-neighbour coupling after the elementary `Nat.dist` shift.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

/-- The centred odd square of radius `n`. -/
abbrev CenteredRect (n : ℕ) := Fin (2 * n + 1) × Fin (2 * n + 1)

/-- Membership in the centred radius-`n` subrectangle of the radius-`m`
rectangle. -/
def centeredIn (n m : ℕ) (p : CenteredRect m) : Prop :=
  m - n ≤ p.1.val ∧ p.1.val ≤ m + n ∧
  m - n ≤ p.2.val ∧ p.2.val ≤ m + n

/-- The exact common-window chart between a smaller centred rectangle and the
corresponding active subtype of a larger one. -/
noncomputable def centeredRectEquiv {n m : ℕ} (h : n ≤ m) :
    CenteredRect n ≃ {p : CenteredRect m // centeredIn n m p} := by
  classical
  let s := m - n
  exact
    { toFun := fun q =>
        ⟨(⟨q.1.val + s, by dsimp [s]; omega⟩,
          ⟨q.2.val + s, by dsimp [s]; omega⟩), by
            dsimp [centeredIn, s]
            omega⟩
      invFun := fun p =>
        (⟨p.1.1.val - s, by
            have hp := p.2
            dsimp [centeredIn, s] at hp
            omega⟩,
         ⟨p.1.2.val - s, by
            have hp := p.2
            dsimp [centeredIn, s] at hp
            omega⟩)
      left_inv := by
        intro q
        apply Prod.ext
        · apply Fin.ext
          dsimp [s]
          omega
        · apply Fin.ext
          dsimp [s]
          omega
      right_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          have hp := p.2
          dsimp [centeredIn, s] at hp ⊢
          omega
        · apply Fin.ext
          have hp := p.2
          dsimp [centeredIn, s] at hp ⊢
          omega }

/-- The nearest-neighbour coupling is unchanged by the centred chart. -/
theorem reindex_active_rectJ
    (β γ : ℝ) {n m : ℕ} (h : n ≤ m) :
    reindexCoupling (centeredRectEquiv h)
        (activeCoupling (rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ)
          (centeredIn n m))
      = rectJ (L := 2 * n + 1) (T := 2 * n + 1) β γ := by
  funext p q
  unfold reindexCoupling activeCoupling rectJ
  change
    (if Nat.dist (p.1.val + (m - n)) (q.1.val + (m - n)) = 1 ∧
          (⟨p.2.val + (m - n), by omega⟩ : Fin (2 * m + 1)) =
            ⟨q.2.val + (m - n), by omega⟩
      then β
      else if
          (⟨p.1.val + (m - n), by omega⟩ : Fin (2 * m + 1)) =
              ⟨q.1.val + (m - n), by omega⟩ ∧
            Nat.dist (p.2.val + (m - n)) (q.2.val + (m - n)) = 1
        then γ else 0) =
      (if Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2 then β
       else if p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1 then γ else 0)
  rw [Nat.dist_add_add_right, Nat.dist_add_add_right]
  simp only [Nat.add_right_cancel_iff, Fin.ext_iff]

/-- Lift an observable on the smaller rectangle to the common outer chart. -/
noncomputable def liftCenteredObservable {n m : ℕ} (h : n ≤ m)
    (g : (CenteredRect n → Fin 2) → ℝ) :
    (CenteredRect m → Fin 2) → ℝ :=
  fun η => g ((configEquiv (centeredRectEquiv h)).symm
    (restrictConfigTo (centeredIn n m) η))

/-- A lifted observable is insensitive to every coordinate outside its centred
support rectangle. -/
theorem deltaAt_liftCenteredObservable_eq_zero_of_not_centered
    {n m : ℕ} (h : n ≤ m) (g : (CenteredRect n → Fin 2) → ℝ)
    (j : CenteredRect m) (hj : ¬ centeredIn n m j) :
    deltaAt j (liftCenteredObservable h g) = 0 := by
  classical
  rw [deltaAt_eq_zero_iff]
  intro η s
  unfold liftCenteredObservable
  apply congrArg g
  apply congrArg (configEquiv (centeredRectEquiv h)).symm
  funext p
  unfold restrictConfigTo
  rw [update_other _ _ _]
  intro hp
  apply hj
  simpa [hp] using p.2

/-- The centred charts compose: lifting first to an intermediate rectangle and
then to the outer rectangle is exactly the direct lift. -/
theorem liftCenteredObservable_comp {r n m : ℕ}
    (hrn : r ≤ n) (hnm : n ≤ m)
    (g : (CenteredRect r → Fin 2) → ℝ) :
    liftCenteredObservable hnm (liftCenteredObservable hrn g) =
      liftCenteredObservable (hrn.trans hnm) g := by
  classical
  funext η
  unfold liftCenteredObservable
  apply congrArg g
  funext p
  change
    η ((centeredRectEquiv hnm) ((centeredRectEquiv hrn p).val)).val =
      η ((centeredRectEquiv (hrn.trans hnm) p).val)
  apply congrArg η
  apply Prod.ext
  · apply Fin.ext
    change p.1.val + (n - r) + (m - n) = p.1.val + (m - r)
    omega
  · apply Fin.ext
    change p.2.val + (n - r) + (m - n) = p.2.val + (m - r)
    omega

/-- A point in the radius-`r` core is at least `n-r` lattice steps from every
row whose radius-`n` restriction can delete a nearest-neighbour interaction. -/
theorem centered_core_dist_to_restriction_defect
    {r n m : ℕ} (hrn : r ≤ n) (hnm : n ≤ m)
    (i j : CenteredRect m) (hj : centeredIn r m j)
    (hdef : ∃ k, rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ i k ≠
      restrictCoupling
        (rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ)
        (centeredIn n m) i k) :
    n - r ≤ rectDist j i := by
  classical
  obtain ⟨k, hk⟩ := hdef
  have hJ : rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ i k ≠ 0 := by
    intro h0
    unfold restrictCoupling at hk
    split at hk <;> simp_all
  have hdik : rectDist i k ≤ 1 := by
    apply Nat.le_of_not_gt
    intro hgt
    exact hJ (rectJ_supp β γ i k hgt)
  have hcut : ¬ (centeredIn n m i ∧ centeredIn n m k) := by
    intro hik
    unfold restrictCoupling at hk
    simp [hik] at hk
  unfold centeredIn at hj hcut
  unfold rectDist Nat.dist at hdik ⊢
  omega

/-- Any two values of a real function differ by at most its oscillation. -/
theorem abs_sub_le_osc (g : κ → ℝ) [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (x y : κ) : |g x - g y| ≤ osc g := by
  have hxSup := apply_le_sup g x
  have hySup := apply_le_sup g y
  have hxInf := inf_le_apply g x
  have hyInf := inf_le_apply g y
  rw [abs_le]
  constructor <;> unfold osc <;> linarith

/-- The total coordinate oscillation of a lifted observable is bounded by the
fixed cardinality of its original support times its global oscillation.  In
particular this bound does not grow with the ambient volume. -/
theorem sum_deltaAt_liftCenteredObservable_le
    {n m : ℕ} (h : n ≤ m) (g : (CenteredRect n → Fin 2) → ℝ) :
    ∑ j, deltaAt j (liftCenteredObservable h g) ≤
      (Fintype.card (CenteredRect n) : ℝ) * osc g := by
  classical
  let A := centeredIn n m
  have hpoint : ∀ j : CenteredRect m,
      deltaAt j (liftCenteredObservable h g) ≤
        if A j then osc g else 0 := by
    intro j
    by_cases hj : A j
    · rw [if_pos hj]
      apply deltaAt_le
      intro η s
      unfold liftCenteredObservable
      exact abs_sub_le_osc g _ _
    · rw [if_neg hj, deltaAt_liftCenteredObservable_eq_zero_of_not_centered h g j hj]
  calc
    ∑ j, deltaAt j (liftCenteredObservable h g)
        ≤ ∑ j, if A j then osc g else 0 :=
          Finset.sum_le_sum fun j _ => hpoint j
    _ = ∑ j ∈ Finset.univ.filter A, osc g := by
      simp only [Finset.sum_filter]
    _ = ∑ _j : {j : CenteredRect m // A j}, osc g := by
      rw [Finset.sum_subtype (p := A) (Finset.univ.filter A) (by simp)]
    _ = (Fintype.card {j : CenteredRect m // A j} : ℝ) * osc g := by
      simp
    _ = (Fintype.card (CenteredRect n) : ℝ) * osc g := by
      congr 1
      norm_cast
      exact (Fintype.card_congr (centeredRectEquiv h)).symm

/-- **D-7, concrete two-rectangle comparison.**  The outer free rectangle is
compared to the genuine smaller free rectangle.  The remaining premise is a
direct support-to-cut distance statement for the supplied observable; it is
not a Cauchy or limit hypothesis. -/
theorem centered_rect_volume_comparison
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    {n m : ℕ} (hnm : n ≤ m)
    (g : (CenteredRect n → Fin 2) → ℝ) (R : ℕ)
    (hfar : ∀ i j : CenteredRect m,
      (∃ k, rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ i k ≠
        restrictCoupling (rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ)
          (centeredIn n m) i k) →
      deltaAt j (liftCenteredObservable hnm g) ≠ 0 →
      R ≤ rectDist j i) :
    |expect (gibbsMu (isingWeight
          (rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ)))
        (liftCenteredObservable hnm g)
      - expect (gibbsMu (isingWeight
          (rectJ (L := 2 * n + 1) (T := 2 * n + 1) β γ))) g|
      ≤ (α ^ R / (1 - α)) *
          ∑ j, deltaAt j (liftCenteredObservable hnm g) := by
  classical
  let e := centeredRectEquiv hnm
  let A := centeredIn n m
  let Jm := rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ
  let gA : ({p : CenteredRect m // A p} → Fin 2) → ℝ :=
    fun η => g ((configEquiv e).symm η)
  letI : Nonempty {p : CenteredRect m // A p} :=
    ⟨e (0, 0)⟩
  have hcomp := ising_active_volume_comparison Jm
    (rectJ_diag β γ) (rectJ_symm β γ) hα0 hα1
    (fun i => le_trans (rectJ_row β γ i) hwin)
    rectDist rectDist_self rectDist_triangle (rectJ_supp β γ)
    A gA R hfar
  have hreindex := expect_gibbs_reindex e (activeCoupling Jm A) gA
  have hsmall :
      expect (gibbsMu (isingWeight (activeCoupling Jm A))) gA =
        expect (gibbsMu (isingWeight
          (rectJ (L := 2 * n + 1) (T := 2 * n + 1) β γ))) g := by
    rw [← hreindex, reindex_active_rectJ β γ hnm]
    simp [gA]
  change
    |expect (gibbsMu (isingWeight Jm)) (liftCenteredObservable hnm g)
      - expect (gibbsMu (isingWeight
          (rectJ (L := 2 * n + 1) (T := 2 * n + 1) β γ))) g|
      ≤ _
  rw [← hsmall]
  exact hcomp

/-- **D-7, local-observable two-volume estimate.**  A single observable on a
fixed radius-`r` core is lifted into two larger free rectangles.  The error is
uniform in the outer radius and decays with the distance `n-r` to the smaller
boundary. -/
theorem centered_local_observable_comparison
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    {r n m : ℕ} (hrn : r ≤ n) (hnm : n ≤ m)
    (g : (CenteredRect r → Fin 2) → ℝ) :
    |expect (gibbsMu (isingWeight
          (rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ)))
        (liftCenteredObservable (hrn.trans hnm) g)
      - expect (gibbsMu (isingWeight
          (rectJ (L := 2 * n + 1) (T := 2 * n + 1) β γ)))
        (liftCenteredObservable hrn g)|
      ≤ (α ^ (n - r) / (1 - α)) *
          ((Fintype.card (CenteredRect r) : ℝ) * osc g) := by
  classical
  have hfar : ∀ i j : CenteredRect m,
      (∃ k, rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ i k ≠
        restrictCoupling
          (rectJ (L := 2 * m + 1) (T := 2 * m + 1) β γ)
          (centeredIn n m) i k) →
      deltaAt j
          (liftCenteredObservable hnm (liftCenteredObservable hrn g)) ≠ 0 →
      n - r ≤ rectDist j i := by
    intro i j hdef hj
    apply centered_core_dist_to_restriction_defect hrn hnm i j
    · by_contra hjcore
      apply hj
      rw [liftCenteredObservable_comp hrn hnm]
      exact deltaAt_liftCenteredObservable_eq_zero_of_not_centered
        (hrn.trans hnm) g j hjcore
    · exact hdef
  have hcmp := centered_rect_volume_comparison β γ α hα0 hα1 hwin hnm
    (liftCenteredObservable hrn g) (n - r) hfar
  rw [liftCenteredObservable_comp hrn hnm] at hcmp
  refine hcmp.trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact sum_deltaAt_liftCenteredObservable_le (hrn.trans hnm) g
  · exact div_nonneg (pow_nonneg hα0 _) (by linarith)

end Dobrushin

end YangMills.OS
