/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.DobrushinIsing

/-!
# D-5 — the volume family: the anisotropic Ising rectangle, with the window
fixed before the volume

Charter lineage: `docs/DOBRUSHIN-D3-CHARTER.md`.  Gates: G15/G16/G17 of
`scripts/judge_dobrushin_d5.py`, committed before any Lean of this rung
(`e7c486e1f`).

## What this module is for

D-4b proves decay for the Ising weight of ONE coupling matrix.  A physical
statement quantifies over a FAMILY of volumes.  This module supplies the
family: the `L × T` rectangle with coupling `β` on horizontal nearest
neighbours, `γ` on vertical ones, free boundary, and the Manhattan distance.
Its content:

* `rectJ_row` — the envelope row sum is at most the lane's window
  `2 tanh|β| + 2 tanh|γ|` at EVERY site of EVERY rectangle: each site has at
  most two horizontal and two vertical bonds, counted by injecting the
  neighbour sets into two-element sets of naturals;
* `rect_ising_uniform_two_point` / `rect_ising_uniform_decay` — the D-4b
  endpoints applied so that `β`, `γ`, `α` and the prefactor are fixed
  \emph{before} the quantifier over `(L, T)`: the uniformity in the volume is
  carried by the quantifier order of the statement itself, not by a phrase;
* `rect_zero_coupling_indep` — non-vacuity across the whole family: at zero
  coupling the endpoint FORCES exact independence of distinct single-site
  observables at every volume, because the bound degenerates to `0^d = 0`.

## What this module does NOT claim

Nothing about the transfer operator: the statements are about correlations of
the Gibbs weight of each finite rectangle.  Nothing about the ordered phase:
the window is a sufficient high-temperature condition.  No claim that the
window is optimal.  The spectral transport is D-6's, declared separately.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

/-! ## §1  The rectangle: distance and coupling -/

/-- Manhattan distance on the `L × T` rectangle. -/
def rectDist {L T : ℕ} (p q : Fin L × Fin T) : ℕ :=
  Nat.dist p.1.val q.1.val + Nat.dist p.2.val q.2.val

theorem rectDist_self {L T : ℕ} (p : Fin L × Fin T) : rectDist p p = 0 := by
  unfold rectDist
  rw [Nat.dist_self, Nat.dist_self]

theorem rectDist_triangle {L T : ℕ} (p q r : Fin L × Fin T) :
    rectDist p r ≤ rectDist p q + rectDist q r := by
  unfold rectDist
  have h1 := Nat.dist.triangle_inequality p.1.val q.1.val r.1.val
  have h2 := Nat.dist.triangle_inequality p.2.val q.2.val r.2.val
  omega

theorem rectDist_eq_zero_iff {L T : ℕ} (p q : Fin L × Fin T) :
    rectDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold rectDist at h
    have h1 : Nat.dist p.1.val q.1.val = 0 := by omega
    have h2 : Nat.dist p.2.val q.2.val = 0 := by omega
    unfold Nat.dist at h1 h2
    refine Prod.ext ?_ ?_
    · exact Fin.val_injective (by omega)
    · exact Fin.val_injective (by omega)
  · intro h
    subst h
    exact rectDist_self p

/-- The rectangle coupling: `β` across horizontal nearest neighbours, `γ`
across vertical ones, zero elsewhere.  Free boundary: edge sites simply have
fewer neighbours. -/
noncomputable def rectJ {L T : ℕ} (β γ : ℝ) :
    (Fin L × Fin T) → (Fin L × Fin T) → ℝ :=
  fun p q =>
    if Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2 then β
    else if p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1 then γ else 0

theorem rectJ_diag {L T : ℕ} (β γ : ℝ) :
    ∀ p : Fin L × Fin T, rectJ β γ p p = 0 := by
  intro p
  unfold rectJ
  have h1 : ¬(Nat.dist p.1.val p.1.val = 1 ∧ p.2 = p.2) := by
    rintro ⟨h, -⟩
    rw [Nat.dist_self] at h
    exact one_ne_zero h.symm
  have h2 : ¬(p.1 = p.1 ∧ Nat.dist p.2.val p.2.val = 1) := by
    rintro ⟨-, h⟩
    rw [Nat.dist_self] at h
    exact one_ne_zero h.symm
  rw [if_neg h1, if_neg h2]

theorem rectJ_symm {L T : ℕ} (β γ : ℝ) :
    ∀ p q : Fin L × Fin T, rectJ β γ p q = rectJ β γ q p := by
  intro p q
  unfold rectJ
  rw [Nat.dist_comm p.1.val q.1.val, Nat.dist_comm p.2.val q.2.val]
  have e1 : (Nat.dist q.1.val p.1.val = 1 ∧ p.2 = q.2)
      ↔ (Nat.dist q.1.val p.1.val = 1 ∧ q.2 = p.2) := by
    constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, h'.symm⟩
  have e2 : (p.1 = q.1 ∧ Nat.dist q.2.val p.2.val = 1)
      ↔ (q.1 = p.1 ∧ Nat.dist q.2.val p.2.val = 1) := by
    constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h.symm, h'⟩
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]

theorem rectJ_supp {L T : ℕ} (β γ : ℝ) :
    ∀ p q : Fin L × Fin T, 1 < rectDist p q → rectJ β γ p q = 0 := by
  intro p q h
  unfold rectDist at h
  unfold rectJ
  have h1 : ¬(Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2) := by
    rintro ⟨hd, he⟩
    have h0 : Nat.dist p.2.val q.2.val = 0 :=
      Nat.dist_eq_zero (congrArg Fin.val he)
    omega
  have h2 : ¬(p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1) := by
    rintro ⟨he, hd⟩
    have h0 : Nat.dist p.1.val q.1.val = 0 :=
      Nat.dist_eq_zero (congrArg Fin.val he)
    omega
  rw [if_neg h1, if_neg h2]

/-! ## §2  The row sums respect the window

Pointwise, `tanh |rectJ|` is at most a horizontal indicator times `tanh|β|`
plus a vertical one times `tanh|γ|`; each indicator's support injects into a
two-element set of naturals, so each sum is at most twice its coefficient. -/

theorem tanh_rectJ_le {L T : ℕ} (β γ : ℝ) (p q : Fin L × Fin T) :
    Real.tanh |rectJ β γ p q|
      ≤ (if Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2 then Real.tanh |β| else 0)
        + (if p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1 then Real.tanh |γ|
            else 0) := by
  unfold rectJ
  by_cases h1 : Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2
  · have h2 : ¬(p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1) := by
      rintro ⟨he, -⟩
      obtain ⟨hd, -⟩ := h1
      have h0 : Nat.dist p.1.val q.1.val = 0 :=
        Nat.dist_eq_zero (congrArg Fin.val he)
      omega
    rw [if_pos h1, if_pos h1, if_neg h2]
    exact le_add_of_nonneg_right le_rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1
    · rw [if_pos h2, if_pos h2]
      exact le_add_of_nonneg_left le_rfl
    · rw [if_neg h2, if_neg h2]
      rw [abs_zero, tanh_zero']
      norm_num

/-- At most two horizontal neighbours: the neighbour set injects, through the
first coordinate's value, into `{p.1.val - 1, p.1.val + 1}`. -/
theorem card_horiz_le {L T : ℕ} (p : Fin L × Fin T) :
    (Finset.univ.filter (fun q : Fin L × Fin T =>
      Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2)).card ≤ 2 := by
  have hmaps : ∀ q ∈ Finset.univ.filter (fun q : Fin L × Fin T =>
      Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2),
      q.1.val ∈ ({p.1.val - 1, p.1.val + 1} : Finset ℕ) := by
    intro q hq
    have hd := (Finset.mem_filter.mp hq).2.1
    have hcase : q.1.val = p.1.val - 1 ∨ q.1.val = p.1.val + 1 := by
      unfold Nat.dist at hd
      omega
    rcases hcase with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
  have hinj : ∀ q₁ ∈ Finset.univ.filter (fun q : Fin L × Fin T =>
      Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2),
      ∀ q₂ ∈ Finset.univ.filter (fun q : Fin L × Fin T =>
        Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2),
      q₁.1.val = q₂.1.val → q₁ = q₂ := by
    intro q₁ h₁ q₂ h₂ hv
    have he₁ := (Finset.mem_filter.mp h₁).2.2
    have he₂ := (Finset.mem_filter.mp h₂).2.2
    refine Prod.ext (Fin.val_injective hv) ?_
    exact he₁.symm.trans he₂
  have hle := Finset.card_le_card_of_injOn
    (fun q : Fin L × Fin T => q.1.val) hmaps hinj
  have h2 : ({p.1.val - 1, p.1.val + 1} : Finset ℕ).card ≤ 2 := by
    have hins := Finset.card_insert_le (p.1.val - 1)
      ({p.1.val + 1} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega
  omega

/-- At most two vertical neighbours, the mirror argument. -/
theorem card_vert_le {L T : ℕ} (p : Fin L × Fin T) :
    (Finset.univ.filter (fun q : Fin L × Fin T =>
      p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1)).card ≤ 2 := by
  have hmaps : ∀ q ∈ Finset.univ.filter (fun q : Fin L × Fin T =>
      p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1),
      q.2.val ∈ ({p.2.val - 1, p.2.val + 1} : Finset ℕ) := by
    intro q hq
    have hd := (Finset.mem_filter.mp hq).2.2
    have hcase : q.2.val = p.2.val - 1 ∨ q.2.val = p.2.val + 1 := by
      unfold Nat.dist at hd
      omega
    rcases hcase with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
  have hinj : ∀ q₁ ∈ Finset.univ.filter (fun q : Fin L × Fin T =>
      p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1),
      ∀ q₂ ∈ Finset.univ.filter (fun q : Fin L × Fin T =>
        p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1),
      q₁.2.val = q₂.2.val → q₁ = q₂ := by
    intro q₁ h₁ q₂ h₂ hv
    have he₁ := (Finset.mem_filter.mp h₁).2.1
    have he₂ := (Finset.mem_filter.mp h₂).2.1
    refine Prod.ext ?_ (Fin.val_injective hv)
    exact he₁.symm.trans he₂
  have hle := Finset.card_le_card_of_injOn
    (fun q : Fin L × Fin T => q.2.val) hmaps hinj
  have h2 : ({p.2.val - 1, p.2.val + 1} : Finset ℕ).card ≤ 2 := by
    have hins := Finset.card_insert_le (p.2.val - 1)
      ({p.2.val + 1} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega
  omega

/-- **The row sums respect the window at every site of every rectangle.** -/
theorem rectJ_row {L T : ℕ} (β γ : ℝ) :
    ∀ p : Fin L × Fin T, ∑ q, Real.tanh |rectJ β γ p q|
      ≤ 2 * Real.tanh |β| + 2 * Real.tanh |γ| := by
  intro p
  have hb := tanh_nonneg_of_nonneg (abs_nonneg β)
  have hg := tanh_nonneg_of_nonneg (abs_nonneg γ)
  have hH : ∑ q : Fin L × Fin T,
      (if Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2 then Real.tanh |β| else 0)
      ≤ 2 * Real.tanh |β| := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.filter (fun q : Fin L × Fin T =>
        Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2)).card : ℝ) ≤ 2 := by
      exact_mod_cast card_horiz_le p
    exact mul_le_mul_of_nonneg_right hc hb
  have hV : ∑ q : Fin L × Fin T,
      (if p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1 then Real.tanh |γ| else 0)
      ≤ 2 * Real.tanh |γ| := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.filter (fun q : Fin L × Fin T =>
        p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1)).card : ℝ) ≤ 2 := by
      exact_mod_cast card_vert_le p
    exact mul_le_mul_of_nonneg_right hc hg
  calc ∑ q, Real.tanh |rectJ β γ p q|
      ≤ ∑ q : Fin L × Fin T,
          ((if Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2 then Real.tanh |β|
              else 0)
            + (if p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1 then Real.tanh |γ|
                else 0)) :=
        Finset.sum_le_sum fun q _ => tanh_rectJ_le β γ p q
    _ = (∑ q : Fin L × Fin T,
          (if Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2 then Real.tanh |β|
            else 0))
        + ∑ q : Fin L × Fin T,
            (if p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1 then Real.tanh |γ|
              else 0) := Finset.sum_add_distrib
    _ ≤ 2 * Real.tanh |β| + 2 * Real.tanh |γ| := add_le_add hH hV

/-! ## §3  The endpoints: constants first, volumes after

The quantifier order is the theorem.  `β`, `γ`, the window bound `α` and the
prefactor are fixed once; then EVERY rectangle obeys the same bound. -/

/-- **D-5, two-point form.**  Volume-uniform exponential decay for the
anisotropic Ising rectangle family: the rate and prefactor never hear
`(L, T)`. -/
theorem rect_ising_uniform_two_point (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α) :
    ∀ (L T : ℕ), 0 < L → 0 < T →
      ∀ (p₀ q₀ : Fin L × Fin T) (f g : ((Fin L × Fin T) → Fin 2) → ℝ),
        (∀ k, k ≠ p₀ → deltaAt k f = 0) →
        (∀ k, k ≠ q₀ → deltaAt k g = 0) →
        |covar (gibbsMu (isingWeight (rectJ β γ))) f g|
          ≤ deltaAt p₀ f * (α ^ rectDist p₀ q₀ / (1 - α)) * deltaAt q₀ g
              / 4 := by
  intro L T hL hT p₀ q₀ f g hf hg
  haveI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  haveI : Nonempty (Fin T) := Fin.pos_iff_nonempty.mp hT
  exact ising_covar_two_point (rectJ β γ) (rectJ_diag β γ) (rectJ_symm β γ)
    hα0 hα1 (fun p => le_trans (rectJ_row β γ p) hwin)
    rectDist rectDist_self rectDist_triangle (rectJ_supp β γ)
    p₀ q₀ f g hf hg

/-- **D-5, general form**: every pair of observables, every rectangle, one
window. -/
theorem rect_ising_uniform_decay (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α) :
    ∀ (L T : ℕ), 0 < L → 0 < T →
      ∀ f g : ((Fin L × Fin T) → Fin 2) → ℝ,
        |covar (gibbsMu (isingWeight (rectJ β γ))) f g|
          ≤ (∑ i, ∑ j, deltaAt i f * (α ^ rectDist i j / (1 - α)) * deltaAt j g)
              / 4 := by
  intro L T hL hT f g
  haveI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  haveI : Nonempty (Fin T) := Fin.pos_iff_nonempty.mp hT
  exact ising_covar_exp_decay (rectJ β γ) (rectJ_diag β γ) (rectJ_symm β γ)
    hα0 hα1 (fun p => le_trans (rectJ_row β γ p) hwin)
    rectDist rectDist_self rectDist_triangle (rectJ_supp β γ) f g

/-! ## §4  Non-vacuity across the family

At zero coupling the window is `0 ≤ 0`, the rate is `0`, and for distinct
sites the bound reads `|Cov| ≤ 0`: the endpoint FORCES exact independence of
single-site observables at every volume — which is true, and which shows the
family statement carries content at every `(L, T)` simultaneously. -/

theorem rect_zero_coupling_indep :
    ∀ (L T : ℕ), 0 < L → 0 < T →
      ∀ (p₀ q₀ : Fin L × Fin T), p₀ ≠ q₀ →
      ∀ f g : ((Fin L × Fin T) → Fin 2) → ℝ,
        (∀ k, k ≠ p₀ → deltaAt k f = 0) →
        (∀ k, k ≠ q₀ → deltaAt k g = 0) →
        covar (gibbsMu (isingWeight (rectJ 0 0))) f g = 0 := by
  intro L T hL hT p₀ q₀ hne f g hf hg
  have hwin : 2 * Real.tanh |(0 : ℝ)| + 2 * Real.tanh |(0 : ℝ)| ≤ 0 := by
    rw [abs_zero, tanh_zero']
    norm_num
  have h := rect_ising_uniform_two_point 0 0 0 le_rfl one_pos hwin
    L T hL hT p₀ q₀ f g hf hg
  have hd : rectDist p₀ q₀ ≠ 0 := fun h0 =>
    hne ((rectDist_eq_zero_iff p₀ q₀).mp h0)
  have hle : |covar (gibbsMu (isingWeight (rectJ 0 0))) f g| ≤ 0 := by
    calc |covar (gibbsMu (isingWeight (rectJ 0 0))) f g|
        ≤ deltaAt p₀ f * ((0 : ℝ) ^ rectDist p₀ q₀ / (1 - 0)) * deltaAt q₀ g
            / 4 := h
      _ = 0 := by
          rw [zero_pow hd]
          ring
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

end Dobrushin

end YangMills.OS
