/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexWeakenedRandomWalkSeries
import YangMills.RG.BalabanCMP99GeneralizedRandomWalk

/-!
# Difference of a complex weakening monomial from full coupling

The contour defect must vanish with the contour radius.  Bounding the
weakened covariance and the fully coupled covariance separately would lose
that fact.  This file gives the finite telescoping estimate used term by term.
-/

namespace YangMills.RG

open scoped BigOperators

universe u

/-- Exact nonempty-subset expansion of a weakening monomial defect.  Unlike
the later norm estimate, this identity remembers every contour coordinate
that is responsible for the defect and is therefore suitable for a
first-visit factorization of physical walks. -/
theorem cmp116ComplexWeakeningMonomial_sub_one_eq_sum_nonemptySubsets
    {Δ : Type u} [DecidableEq Δ]
    (active : Finset Δ) (sigma : Δ → ℂ) :
    cmp116ComplexWeakeningMonomial active sigma - 1 =
      ∑ subset ∈ active.powerset.erase ∅,
        ∏ d ∈ subset, (sigma d - 1) := by
  classical
  have hfac : ∀ d ∈ active,
      sigma d = (sigma d - 1) + 1 := by
    intro d hd
    ring
  have hfull :
      cmp116ComplexWeakeningMonomial active sigma =
        ∑ subset ∈ active.powerset,
          ∏ d ∈ subset, (sigma d - 1) := by
    rw [cmp116ComplexWeakeningMonomial,
      Finset.prod_congr rfl hfac, Finset.prod_add]
    exact Finset.sum_congr rfl fun subset hsubset => by
      rw [Finset.prod_const_one, mul_one]
  have hempty : (∅ : Finset Δ) ∈ active.powerset := by simp
  have herase :
      (∑ subset ∈ active.powerset, ∏ d ∈ subset, (sigma d - 1)) =
        1 + ∑ subset ∈ active.powerset.erase ∅,
          ∏ d ∈ subset, (sigma d - 1) := by
    rw [← Finset.sum_erase_add _ _ hempty]
    simp
  rw [hfull, herase]
  ring

/-- A weakening monomial differs from one by at most its active cardinality,
the coordinate radius, and a uniform coordinate cap.  The deliberately
stable power `R^|active|` is suited to the later walk-length majorant. -/
theorem norm_cmp116ComplexWeakeningMonomial_sub_one_le
    {Δ : Type u} [DecidableEq Δ]
    (active : Finset Δ) (sigma : Δ → ℂ) (radius R : ℝ)
    (hradius : 0 ≤ radius) (hR : 1 ≤ R)
    (hdiff : ∀ d ∈ active, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d ∈ active, ‖sigma d‖ ≤ R) :
    ‖cmp116ComplexWeakeningMonomial active sigma - 1‖ ≤
      (active.card : ℝ) * radius * R ^ active.card := by
  classical
  induction active using Finset.induction_on with
  | empty =>
      simp [cmp116ComplexWeakeningMonomial]
  | @insert d active hd ih =>
      have hprod :
          ‖cmp116ComplexWeakeningMonomial active sigma‖ ≤
            R ^ active.card := by
        rw [cmp116ComplexWeakeningMonomial, norm_prod]
        simpa using
          (Finset.prod_le_prod
            (fun x _ => norm_nonneg (sigma x))
            (fun x hx => hcap x (Finset.mem_insert_of_mem hx)))
      have hsplit :
          sigma d * cmp116ComplexWeakeningMonomial active sigma - 1 =
            (sigma d - 1) *
                cmp116ComplexWeakeningMonomial active sigma +
              (cmp116ComplexWeakeningMonomial active sigma - 1) := by
        ring
      rw [cmp116ComplexWeakeningMonomial, Finset.prod_insert hd]
      change ‖sigma d * cmp116ComplexWeakeningMonomial active sigma - 1‖ ≤ _
      rw [hsplit]
      calc
        ‖(sigma d - 1) *
                cmp116ComplexWeakeningMonomial active sigma +
              (cmp116ComplexWeakeningMonomial active sigma - 1)‖
            ≤ ‖sigma d - 1‖ *
                  ‖cmp116ComplexWeakeningMonomial active sigma‖ +
                ‖cmp116ComplexWeakeningMonomial active sigma - 1‖ := by
              simpa only [norm_mul] using
                norm_add_le
                  ((sigma d - 1) *
                    cmp116ComplexWeakeningMonomial active sigma)
                  (cmp116ComplexWeakeningMonomial active sigma - 1)
        _ ≤ radius * R ^ active.card +
              (active.card : ℝ) * radius * R ^ active.card := by
            have hfirst :
                ‖sigma d - 1‖ *
                    ‖cmp116ComplexWeakeningMonomial active sigma‖ ≤
                  radius * R ^ active.card :=
              mul_le_mul
                (hdiff d (Finset.mem_insert_self d active))
                hprod (norm_nonneg _) hradius
            have hsecond :
                ‖cmp116ComplexWeakeningMonomial active sigma - 1‖ ≤
                  (active.card : ℝ) * radius * R ^ active.card :=
              ih
                (fun x hx => hdiff x (Finset.mem_insert_of_mem hx))
                (fun x hx => hcap x (Finset.mem_insert_of_mem hx))
            exact add_le_add hfirst hsecond
        _ = ((active.card + 1 : ℕ) : ℝ) *
              radius * R ^ active.card := by
            push_cast
            ring
        _ ≤ ((active.card + 1 : ℕ) : ℝ) *
              radius * R ^ (active.card + 1) := by
            rw [pow_succ]
            have hpow : 0 ≤ R ^ active.card := pow_nonneg (le_trans zero_le_one hR) _
            have hcoef :
                0 ≤ ((active.card + 1 : ℕ) : ℝ) * radius :=
              mul_nonneg (Nat.cast_nonneg _) hradius
            exact mul_le_mul_of_nonneg_left
              (by nlinarith [hpow]) hcoef
        _ = (((insert d active).card : ℕ) : ℝ) *
              radius * R ^ (insert d active).card := by
            rw [Finset.card_insert_of_notMem hd]

/-- Source walk specialization: the literal active-cardinality budget turns
the monomial defect into an explicit function of the walk length. -/
theorem norm_cmp116ComplexWeakeningMonomial_walkActive_sub_one_le
    {Label Domain Cube : Type*}
    [DecidableEq Cube]
    (walk : CMP99GeneralizedWalk Label Domain)
    (domainActive : Domain → Finset Cube)
    (B : ℕ)
    (hactive : ∀ X, (domainActive X).card ≤ B)
    (sigma : Cube → ℂ) (radius R : ℝ)
    (hradius : 0 ≤ radius) (hR : 1 ≤ R)
    (hdiff : ∀ d ∈ walk.active domainActive, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d ∈ walk.active domainActive, ‖sigma d‖ ≤ R) :
    ‖cmp116ComplexWeakeningMonomial
        (walk.active domainActive) sigma - 1‖ ≤
      ((B * (walk.length + 1) : ℕ) : ℝ) * radius *
        R ^ (B * (walk.length + 1)) := by
  have hcard :
      (walk.active domainActive).card ≤ B * (walk.length + 1) :=
    walk.card_active_le_mul_length_add_one domainActive B hactive
  have hbase :=
    norm_cmp116ComplexWeakeningMonomial_sub_one_le
      (walk.active domainActive) sigma radius R hradius hR hdiff hcap
  have hcast :
      ((walk.active domainActive).card : ℝ) ≤
        ((B * (walk.length + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hpow :
      R ^ (walk.active domainActive).card ≤
        R ^ (B * (walk.length + 1)) :=
    pow_le_pow_right₀ hR hcard
  calc
    ‖cmp116ComplexWeakeningMonomial
        (walk.active domainActive) sigma - 1‖
        ≤ ((walk.active domainActive).card : ℝ) * radius *
            R ^ (walk.active domainActive).card := hbase
    _ ≤ ((B * (walk.length + 1) : ℕ) : ℝ) * radius *
          R ^ (B * (walk.length + 1)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hcast hradius)
        hpow
        (pow_nonneg (le_trans zero_le_one hR) _)
        (mul_nonneg (Nat.cast_nonneg _) hradius)

end YangMills.RG
