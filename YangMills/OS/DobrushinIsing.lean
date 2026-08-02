/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.DobrushinGibbs
import YangMills.OS.DobrushinCoefficient
import YangMills.OS.DobrushinRowSum

/-!
# D-4b — the interaction, instantiated: the intrinsic matrix of the Ising
weight is dominated by the envelope, and the window becomes a theorem
about a weight

Charter lineage: `docs/DOBRUSHIN-D3-CHARTER.md`.  Gates: G13/G14 of
`scripts/judge_dobrushin_d4.py`, committed before any Lean of this rung
(`2cda729f5`) and passed in both modes before this file was written.

## What this module is for

`DobrushinGibbs.lean` (D-4a) starts the chain at an ARBITRARY positive weight
and leaves exactly Dobrushin's condition on the intrinsic matrix to its user.
This module instantiates the weight itself: for the Ising weight of a
symmetric zero-diagonal coupling `J`,

* the heat-bath conditional is the SIGMOID OF THE LOCAL FIELD,
  `(1 + tanh h)/2` at `h i = ∑ k J i k · spin (η k)` — G13 as a theorem
  (`heatBath_ising_pPlus`);
* the intrinsic Dobrushin coefficient is dominated by the envelope of
  `DobrushinCoefficient.lean`: `dobCoeff (isingWeight J) i k ≤ tanh |J i k|`
  — G14's entrywise claim as a theorem (`dobCoeff_ising_le`);
* consequently the row-sum hypothesis of every D-4a endpoint becomes a
  COMPUTATION ON `J`: `ising_covar_le_resolvent`, `ising_covar_exp_decay`,
  `ising_covar_two_point`;
* on the one-bond system the domination is an EQUALITY
  (`IsingBondWitness.dobCoeff_bond_attained`): the optimal field `h = β` is
  reachable there, so the envelope is the coefficient itself and the
  non-vacuity witness is sharp; that system satisfies Dobrushin's condition
  at EVERY coupling (`IsingBondWitness.bond_covar_two_point`);
* on the star cell of `DobrushinRowSum.lean` the lane's window
  `2 tanh|β| + 2 tanh|γ| < 1` is the hypothesis of an exponential-decay
  theorem about the anisotropic Ising WEIGHT (`StarWitness.star_covar_two_point`)
  — the composition the abstract of the paper promises, as one declaration.

## What this module does NOT claim

The envelope is a majorant, not the minimum: on multi-bond systems the
reachable fields form a discrete set and `dobCoeff` may be strictly below
`tanh |J|` (G14 measures that gap; nothing here contradicts it).  No
infinite-volume state, no operator transport, no optimality of the window.

## Conventions

Two states, `spin 0 = 1` and `spin 1 = -1`.  The energy is
`(∑ a ∑ b J a b · σ_a σ_b)/2` over ORDERED pairs with `J` symmetric and
zero-diagonal, so each bond is counted once and the local field at `i` is
`∑ k J i k · σ_k` with no stray factor of two — the convention of
`DobrushinCoefficient.lean`, where flipping a neighbour moves the field by
`2J` and the conditional by at most `tanh J`.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ## §1  Spin, field, weight -/

/-- The spin of a two-state site: `+1` at `0`, `-1` at `1`. -/
noncomputable def spin (s : Fin 2) : ℝ := if s = 0 then 1 else -1

theorem spin_zero : spin 0 = 1 := by
  unfold spin
  rw [if_pos rfl]

theorem spin_one : spin 1 = -1 := by
  unfold spin
  rw [if_neg (by decide)]

theorem spin_eq_or (t : Fin 2) : spin t = 1 ∨ spin t = -1 := by
  unfold spin
  by_cases h : t = 0
  · rw [if_pos h]
    exact Or.inl rfl
  · rw [if_neg h]
    exact Or.inr rfl

/-- The move of one spin is `0` or `±2` — the discreteness that turns the
field move into the `h - 2J` of the envelope. -/
theorem spin_sub_cases (t r : Fin 2) :
    spin t - spin r = 0 ∨ spin t - spin r = 2 ∨ spin t - spin r = -2 := by
  rcases spin_eq_or t with ht | ht <;> rcases spin_eq_or r with hr | hr <;>
    rw [ht, hr] <;> norm_num

/-- The local field at `i`: every bond into `i`, read at the configuration. -/
noncomputable def localField (J : ι → ι → ℝ) (η : ι → Fin 2) (i : ι) : ℝ :=
  ∑ k, J i k * spin (η k)

/-- The Ising weight.  Ordered pairs, halved: each bond once. -/
noncomputable def isingWeight (J : ι → ι → ℝ) (η : ι → Fin 2) : ℝ :=
  Real.exp ((∑ a, ∑ b, J a b * spin (η a) * spin (η b)) / 2)

theorem isingWeight_pos (J : ι → ι → ℝ) (η : ι → Fin 2) :
    0 < isingWeight J η := Real.exp_pos _

/-- The energy of the bonds that do not touch `i`. -/
noncomputable def offEnergy (J : ι → ι → ℝ) (η : ι → Fin 2) (i : ι) : ℝ :=
  (∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i,
    J a b * spin (η a) * spin (η b)) / 2

/-! ## §2  The energy splits at one site

The quadratic energy of an updated configuration is an `s`-free block plus a
LINEAR term in `spin s`, whose coefficient is the local field.  This is the
only structural computation of the module; everything after it is the
envelope. -/

theorem energy_update (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) (η : ι → Fin 2) (i : ι) (s : Fin 2) :
    (∑ a, ∑ b, J a b * spin (Function.update η i s a)
      * spin (Function.update η i s b)) / 2
      = spin s * localField J η i + offEnergy J η i := by
  classical
  -- the inner sum at a fixed `a ≠ i`, split at `b = i`
  have hib : ∀ a : ι, a ≠ i →
      ∑ b, J a b * spin (Function.update η i s a) * spin (Function.update η i s b)
        = (∑ b ∈ Finset.univ.erase i, J a b * spin (η a) * spin (η b))
          + J a i * spin (η a) * spin s := by
    intro a ha
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · exact Finset.sum_congr rfl fun b hb => by
        rw [update_other η i s ha, update_other η i s (Finset.ne_of_mem_erase hb)]
    · rw [update_other η i s ha, update_self' η i s]
  -- the inner sum at `a = i`, split at `b = i`
  have hii : ∑ b, J i b * spin (Function.update η i s i)
        * spin (Function.update η i s b)
      = (∑ b ∈ Finset.univ.erase i, J i b * spin s * spin (η b))
        + J i i * spin s * spin s := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · exact Finset.sum_congr rfl fun b hb => by
        rw [update_self' η i s, update_other η i s (Finset.ne_of_mem_erase hb)]
    · rw [update_self' η i s]
  -- the outer sum, split at `a = i`; assembled by rewrites, not `congr`
  have herase1 : ∑ a ∈ Finset.univ.erase i,
        (∑ b, J a b * spin (Function.update η i s a)
          * spin (Function.update η i s b))
      = ∑ a ∈ Finset.univ.erase i,
          ((∑ b ∈ Finset.univ.erase i, J a b * spin (η a) * spin (η b))
            + J a i * spin (η a) * spin s) :=
    Finset.sum_congr rfl fun a ha => hib a (Finset.ne_of_mem_erase ha)
  have houter : ∑ a, ∑ b, J a b * spin (Function.update η i s a)
        * spin (Function.update η i s b)
      = (∑ a ∈ Finset.univ.erase i,
          ((∑ b ∈ Finset.univ.erase i, J a b * spin (η a) * spin (η b))
            + J a i * spin (η a) * spin s))
        + ((∑ b ∈ Finset.univ.erase i, J i b * spin s * spin (η b))
            + J i i * spin s * spin s) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i), herase1, hii]
  -- distribute, symmetrise, and read off the field
  have hsplit2 : ∑ a ∈ Finset.univ.erase i,
        ((∑ b ∈ Finset.univ.erase i, J a b * spin (η a) * spin (η b))
          + J a i * spin (η a) * spin s)
      = (∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i,
          J a b * spin (η a) * spin (η b))
        + ∑ a ∈ Finset.univ.erase i, J a i * spin (η a) * spin s :=
    Finset.sum_add_distrib
  have hsymm_sum : ∑ a ∈ Finset.univ.erase i, J a i * spin (η a) * spin s
      = spin s * ∑ a ∈ Finset.univ.erase i, J i a * spin (η a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [hsymm a i]; ring
  have hfield2 : ∑ b ∈ Finset.univ.erase i, J i b * spin s * spin (η b)
      = spin s * ∑ b ∈ Finset.univ.erase i, J i b * spin (η b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hlf : localField J η i = ∑ k ∈ Finset.univ.erase i, J i k * spin (η k) := by
    unfold localField
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i), hdiag i]
    ring
  rw [houter, hsplit2, hsymm_sum, hfield2, hlf, hdiag i]
  unfold offEnergy
  ring

/-- The weight at an updated site factorises: an `s`-free factor times the
exponential of the field term. -/
theorem isingWeight_update (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) (η : ι → Fin 2) (i : ι) (s : Fin 2) :
    isingWeight J (Function.update η i s)
      = Real.exp (offEnergy J η i) * Real.exp (spin s * localField J η i) := by
  unfold isingWeight
  rw [energy_update J hdiag hsymm η i s, Real.exp_add]
  ring

/-! ## §3  The heat-bath conditional is the sigmoid of the field — G13 -/

theorem localZ_ising (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) (i : ι) (η : ι → Fin 2) :
    localZ (isingWeight J) i η
      = Real.exp (offEnergy J η i)
        * (Real.exp (localField J η i) + Real.exp (-localField J η i)) := by
  unfold localZ
  rw [Fin.sum_univ_two, isingWeight_update J hdiag hsymm η i 0,
    isingWeight_update J hdiag hsymm η i 1, spin_zero, spin_one,
    one_mul, neg_one_mul]
  ring

theorem heatBath_ising (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) (i : ι) (η : ι → Fin 2) (s : Fin 2) :
    heatBath (isingWeight J) i η s
      = Real.exp (spin s * localField J η i)
        / (Real.exp (localField J η i) + Real.exp (-localField J η i)) := by
  unfold heatBath
  rw [isingWeight_update J hdiag hsymm η i s, localZ_ising J hdiag hsymm i η]
  have hA : Real.exp (offEnergy J η i) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hD : Real.exp (localField J η i) + Real.exp (-localField J η i) ≠ 0 :=
    ne_of_gt (by positivity)
  field_simp

/-- The exponential ratio is the sigmoid. -/
theorem exp_ratio_pPlus (h : ℝ) :
    Real.exp h / (Real.exp h + Real.exp (-h)) = pPlus h := by
  unfold pPlus
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hc : Real.exp h + Real.exp (-h) ≠ 0 := ne_of_gt (by positivity)
  have hc2 : (Real.exp h + Real.exp (-h)) / 2 ≠ 0 := div_ne_zero hc two_ne_zero
  field_simp
  ring

/-- **G13 as a theorem**: the heat-bath conditional of the Ising weight is
`(1 + tanh h)/2` at the local field. -/
theorem heatBath_ising_pPlus (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) (i : ι) (η : ι → Fin 2) :
    heatBath (isingWeight J) i η 0 = pPlus (localField J η i) := by
  rw [heatBath_ising J hdiag hsymm i η 0, spin_zero, one_mul, exp_ratio_pPlus]

/-! ## §4  Total variation of two-point conditionals is the field move -/

/-- For two normalised two-point distributions the total variation is the
difference of either mass. -/
theorem TV_two_point (p q : Fin 2 → ℝ) (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    TV p q = |p 0 - q 0| := by
  unfold TV
  rw [Fin.sum_univ_two] at hp hq
  rw [Fin.sum_univ_two]
  have h1 : p 1 - q 1 = -(p 0 - q 0) := by linarith
  rw [h1, abs_neg]
  ring

/-- The total variation between the conditionals at two configurations is
exactly the envelope's `tvField` at the two local fields. -/
theorem TV_heatBath_ising (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) (i : ι) (η η' : ι → Fin 2) :
    TV (heatBath (isingWeight J) i η) (heatBath (isingWeight J) i η')
      = tvField (localField J η i) (localField J η' i) := by
  have hw : ∀ ζ : ι → Fin 2, 0 < isingWeight J ζ := fun ζ => isingWeight_pos J ζ
  rw [TV_two_point _ _ (heatBath_sum_one hw i η) (heatBath_sum_one hw i η'),
    heatBath_ising_pPlus J hdiag hsymm i η, heatBath_ising_pPlus J hdiag hsymm i η']
  rfl

/-- Updating site `k` moves the field at `i` by the bond times the spin move. -/
theorem localField_update (J : ι → ι → ℝ) (η : ι → Fin 2) (i k : ι) (t : Fin 2) :
    localField J (Function.update η k t) i
      = localField J η i + J i k * (spin t - spin (η k)) := by
  unfold localField
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ k),
    ← Finset.sum_erase_add Finset.univ (fun m => J i m * spin (η m))
      (Finset.mem_univ k)]
  have herase : ∑ m ∈ Finset.univ.erase k, J i m * spin (Function.update η k t m)
      = ∑ m ∈ Finset.univ.erase k, J i m * spin (η m) :=
    Finset.sum_congr rfl fun m hm => by
      rw [update_other η k t (Finset.ne_of_mem_erase hm)]
  rw [herase, update_self' η k t]
  ring

/-! ## §5  The envelope, at a general-signed move -/

theorem tvField_self (h : ℝ) : tvField h h = 0 := by
  unfold tvField
  rw [sub_self, abs_zero]

theorem tvField_comm (h h' : ℝ) : tvField h h' = tvField h' h := by
  unfold tvField
  exact abs_sub_comm _ _

theorem tanh_zero' : Real.tanh 0 = 0 := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_zero, zero_div]

/-- `tvField h (h - 2J) ≤ tanh |J|` with no sign hypothesis: the negative case
is the positive one read from the other endpoint. -/
theorem tvField_le_abs (J h : ℝ) : tvField h (h - 2 * J) ≤ Real.tanh |J| := by
  rcases le_or_gt 0 J with hJ | hJ
  · rw [abs_of_nonneg hJ]
    exact tvField_le hJ h
  · rw [abs_of_neg hJ]
    have key := tvField_le (J := -J) (by linarith) (h - 2 * J)
    have harg : h - 2 * J - 2 * -J = h := by ring
    rw [harg] at key
    rw [tvField_comm]
    exact key

/-! ## §6  D-4b: the intrinsic matrix is dominated by the envelope — G14 -/

/-- **The entrywise bound.**  The intrinsic Dobrushin coefficient of the Ising
weight is at most the bond envelope `tanh |J i k|`. -/
theorem dobCoeff_ising_le (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) (i k : ι) :
    dobCoeff (isingWeight J) i k ≤ Real.tanh |J i k| := by
  refine Finset.sup'_le _ _ fun q _ => ?_
  rw [TV_heatBath_ising J hdiag hsymm i q.1 (Function.update q.1 k q.2),
    localField_update J q.1 i k q.2]
  rcases spin_sub_cases q.2 (q.1 k) with hD | hD | hD <;> rw [hD]
  · rw [mul_zero, add_zero, tvField_self]
    exact tanh_nonneg_of_nonneg (abs_nonneg _)
  · have key := tvField_le_abs (-(J i k)) (localField J q.1 i)
    rw [abs_neg] at key
    have harg : localField J q.1 i - 2 * -(J i k)
        = localField J q.1 i + J i k * 2 := by ring
    rw [harg] at key
    exact key
  · have key := tvField_le_abs (J i k) (localField J q.1 i)
    have harg : localField J q.1 i - 2 * J i k
        = localField J q.1 i + J i k * -2 := by ring
    rw [harg] at key
    exact key

/-- Where the coupling vanishes, the intrinsic coefficient vanishes. -/
theorem dobCoeff_ising_zero (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) (i k : ι) (h0 : J i k = 0) :
    dobCoeff (isingWeight J) i k = 0 := by
  refine le_antisymm ?_ (dobCoeff_nonneg _ i k)
  have hle := dobCoeff_ising_le J hdiag hsymm i k
  rw [h0, abs_zero, tanh_zero'] at hle
  exact hle

/-- The row-sum hypothesis of D-4a becomes a computation on `J`. -/
theorem dobCoeff_ising_row_le (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) {α : ℝ} (i : ι)
    (hrow : ∑ k, Real.tanh |J i k| ≤ α) :
    ∑ k, dobCoeff (isingWeight J) i k ≤ α :=
  le_trans (Finset.sum_le_sum fun k _ => dobCoeff_ising_le J hdiag hsymm i k) hrow

/-! ## §7  The instantiated endpoints: the hypotheses are computations on `J` -/

/-- **D-4b, series form.**  For the Ising weight of a symmetric zero-diagonal
coupling whose ENVELOPE row sums are at most `α < 1`, connected correlations
obey the comparison estimate. -/
theorem ising_covar_le_resolvent (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, Real.tanh |J i k| ≤ α) (f g : (ι → Fin 2) → ℝ) :
    |covar (gibbsMu (isingWeight J)) f g|
      ≤ (∑ i, ∑ j, deltaAt i f
          * (∑' n : ℕ, ((dobMatrixOf (isingWeight J)) ^ n) i j)
          * deltaAt j g) / 4 :=
  gibbs_covar_le_resolvent (fun η => isingWeight_pos J η) hα0 hα1
    (fun i => dobCoeff_ising_row_le J hdiag hsymm i (hrow i)) f g

/-- **D-4b, distance form.**  Coupling of range one, envelope row sums inside
the window: exponential decay of correlations in the distance. -/
theorem ising_covar_exp_decay (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, Real.tanh |J i k| ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hJsupp : ∀ i j, 1 < d i j → J i j = 0)
    (f g : (ι → Fin 2) → ℝ) :
    |covar (gibbsMu (isingWeight J)) f g|
      ≤ (∑ i, ∑ j, deltaAt i f * (α ^ (d i j) / (1 - α)) * deltaAt j g) / 4 :=
  gibbs_covar_exp_decay (fun η => isingWeight_pos J η) hα0 hα1
    (fun i => dobCoeff_ising_row_le J hdiag hsymm i (hrow i))
    d hself htri
    (fun i j hd => dobCoeff_ising_zero J hdiag hsymm i j (hJsupp i j hd)) f g

/-- **D-4b, two-point form.**  For single-site observables the decay is read
off the bond data alone. -/
theorem ising_covar_two_point (J : ι → ι → ℝ) (hdiag : ∀ a, J a a = 0)
    (hsymm : ∀ a b, J a b = J b a) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, Real.tanh |J i k| ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hJsupp : ∀ i j, 1 < d i j → J i j = 0)
    (i₀ j₀ : ι) (f g : (ι → Fin 2) → ℝ)
    (hf : ∀ k, k ≠ i₀ → deltaAt k f = 0)
    (hg : ∀ k, k ≠ j₀ → deltaAt k g = 0) :
    |covar (gibbsMu (isingWeight J)) f g|
      ≤ deltaAt i₀ f * (α ^ (d i₀ j₀) / (1 - α)) * deltaAt j₀ g / 4 :=
  gibbs_covar_two_point (fun η => isingWeight_pos J η) hα0 hα1
    (fun i => dobCoeff_ising_row_le J hdiag hsymm i (hrow i))
    d hself htri
    (fun i j hd => dobCoeff_ising_zero J hdiag hsymm i j (hJsupp i j hd))
    i₀ j₀ f g hf hg

/-! ## §8  The one-bond witness: domination is an EQUALITY there

Two sites, one bond `β`.  The neighbour's two spins give the fields `±β`, so
the optimal pair of the envelope is REACHED and the intrinsic coefficient is
`tanh β` itself, not merely below it.  And the envelope row sum is `tanh |β|`,
strictly inside the window at EVERY coupling: the decay endpoint for this
system carries no smallness hypothesis at all. -/

namespace IsingBondWitness

/-- One bond of strength `β` between two sites. -/
noncomputable def bondJ (β : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i k => if i = k then 0 else β

theorem bondJ_diag (β : ℝ) : ∀ a, bondJ β a a = 0 := fun a => by
  unfold bondJ
  rw [if_pos rfl]

theorem bondJ_symm (β : ℝ) : ∀ a b, bondJ β a b = bondJ β b a := by
  intro a b
  unfold bondJ
  by_cases h : a = b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun hb => h hb.symm]

theorem bondJ_off (β : ℝ) : bondJ β 0 1 = β := by
  unfold bondJ
  rw [if_neg (by decide)]

theorem bondJ_off' (β : ℝ) : bondJ β 1 0 = β := by
  unfold bondJ
  rw [if_neg (by decide)]

theorem bondJ_row0 (β : ℝ) :
    ∑ k, Real.tanh |bondJ β 0 k| = Real.tanh |β| := by
  rw [Fin.sum_univ_two, bondJ_diag β 0, bondJ_off β, abs_zero, tanh_zero',
    zero_add]

theorem bondJ_row1 (β : ℝ) :
    ∑ k, Real.tanh |bondJ β 1 k| = Real.tanh |β| := by
  rw [Fin.sum_univ_two, bondJ_off' β, bondJ_diag β 1, abs_zero, tanh_zero',
    add_zero]

/-- The envelope row sum of the one-bond system is `tanh |β|` — inside the
window at every coupling. -/
theorem bondJ_row (β : ℝ) (i : Fin 2) :
    ∑ k, Real.tanh |bondJ β i k| = Real.tanh |β| := by
  fin_cases i
  · exact bondJ_row0 β
  · exact bondJ_row1 β

/-- **Attainment.**  On the one-bond system the intrinsic coefficient EQUALS
the envelope: the all-up configuration realises the optimal field `β`, and
flipping the neighbour realises `-β`. -/
theorem dobCoeff_bond_attained (β : ℝ) (hβ : 0 ≤ β) :
    dobCoeff (isingWeight (bondJ β)) 0 1 = Real.tanh β := by
  refine le_antisymm ?_ ?_
  · have h := dobCoeff_ising_le (bondJ β) (bondJ_diag β) (bondJ_symm β) 0 1
    rw [bondJ_off β, abs_of_nonneg hβ] at h
    exact h
  · have hTV : TV (heatBath (isingWeight (bondJ β)) 0 (fun _ => 0))
        (heatBath (isingWeight (bondJ β)) 0
          (Function.update (fun _ : Fin 2 => (0 : Fin 2)) 1 1))
        = Real.tanh β := by
      rw [TV_heatBath_ising (bondJ β) (bondJ_diag β) (bondJ_symm β) 0 _ _]
      have hf1 : localField (bondJ β) (fun _ => 0) 0 = β := by
        unfold localField
        rw [Fin.sum_univ_two]
        simp only []
        rw [bondJ_diag β 0, bondJ_off β, spin_zero]
        ring
      have hf2 : localField (bondJ β)
          (Function.update (fun _ : Fin 2 => (0 : Fin 2)) 1 1) 0 = -β := by
        rw [localField_update (bondJ β) (fun _ => 0) 0 1 1]
        rw [hf1, bondJ_off β, spin_one, spin_zero]
        ring
      rw [hf1, hf2]
      have hatt := tvField_attained hβ
      rw [show β - 2 * β = -β from by ring] at hatt
      exact hatt
    have hpair := Finset.le_sup'
      (fun q : (Fin 2 → Fin 2) × Fin 2 =>
        TV (heatBath (isingWeight (bondJ β)) 0 q.1)
          (heatBath (isingWeight (bondJ β)) 0 (Function.update q.1 1 q.2)))
      (Finset.mem_univ ((⟨fun _ => 0, 1⟩ : (Fin 2 → Fin 2) × Fin 2)))
    rw [hTV] at hpair
    exact hpair

/-- The discrete distance on the two sites. -/
def bondDist (i j : Fin 2) : ℕ := if i = j then 0 else 1

theorem bondDist_self (i : Fin 2) : bondDist i i = 0 := by
  unfold bondDist
  rw [if_pos rfl]

theorem bondDist_triangle (i j k : Fin 2) :
    bondDist i k ≤ bondDist i j + bondDist j k := by
  revert i j k
  decide

theorem bondDist_le_one (i j : Fin 2) : bondDist i j ≤ 1 := by
  revert i j
  decide

/-- **The one-bond system decays at EVERY coupling**: Dobrushin's condition
holds with `α = tanh |β| < 1` unconditionally, so the two-point bound carries
no smallness hypothesis. -/
theorem bond_covar_two_point (β : ℝ) (i₀ j₀ : Fin 2)
    (f g : (Fin 2 → Fin 2) → ℝ)
    (hf : ∀ k, k ≠ i₀ → deltaAt k f = 0)
    (hg : ∀ k, k ≠ j₀ → deltaAt k g = 0) :
    |covar (gibbsMu (isingWeight (bondJ β))) f g|
      ≤ deltaAt i₀ f
          * (Real.tanh |β| ^ (bondDist i₀ j₀) / (1 - Real.tanh |β|))
          * deltaAt j₀ g / 4 :=
  ising_covar_two_point (bondJ β) (bondJ_diag β) (bondJ_symm β)
    (tanh_nonneg_of_nonneg (abs_nonneg β)) (Real.tanh_lt_one _)
    (fun i => le_of_eq (bondJ_row β i))
    bondDist bondDist_self bondDist_triangle
    (fun i j hd => absurd hd (by
      have hle := bondDist_le_one i j
      omega))
    i₀ j₀ f g hf hg

end IsingBondWitness

/-! ## §9  The star witness: the lane's window, instantiated at a weight

The star cell of `DobrushinRowSum.lean` — a centre with two bonds `β` and two
bonds `γ` — carried the row-sum computation `2 tanh|β| + 2 tanh|γ|`.  Here
that number becomes the hypothesis of a decay theorem about the anisotropic
Ising WEIGHT on the star: the window of the lane, as one declaration. -/

namespace StarWitness

/-- The star coupling: `starBond` masked to the star's edges.  Symmetric,
zero-diagonal, range one for `starDist`. -/
noncomputable def starJ (β γ : ℝ) : Fin 5 → Fin 5 → ℝ :=
  fun i j => if starDist i j = 1 then starBond β γ i j else 0

theorem starDist_comm (i j : Fin 5) : starDist i j = starDist j i := by
  revert i j
  decide

theorem starBond_comm (β γ : ℝ) (i j : Fin 5) :
    starBond β γ i j = starBond β γ j i := by
  unfold starBond
  by_cases h : i = 1 ∨ j = 1 ∨ i = 2 ∨ j = 2
  · rw [if_pos h, if_pos (by tauto)]
  · rw [if_neg h, if_neg (by tauto)]

theorem starJ_diag (β γ : ℝ) : ∀ a, starJ β γ a a = 0 := fun a => by
  unfold starJ
  rw [starDist_self a, if_neg (by decide)]

theorem starJ_symm (β γ : ℝ) : ∀ a b, starJ β γ a b = starJ β γ b a := by
  intro a b
  unfold starJ
  rw [starDist_comm a b]
  by_cases h : starDist b a = 1
  · rw [if_pos h, if_pos h, starBond_comm]
  · rw [if_neg h, if_neg h]

theorem starJ_supp (β γ : ℝ) :
    ∀ i j, 1 < starDist i j → starJ β γ i j = 0 := by
  intro i j h
  unfold starJ
  rw [if_neg (by omega)]

theorem starJ_01 (β γ : ℝ) : starJ β γ 0 1 = β := by
  unfold starJ starBond
  rw [if_pos (by decide), if_pos (by decide)]

theorem starJ_02 (β γ : ℝ) : starJ β γ 0 2 = β := by
  unfold starJ starBond
  rw [if_pos (by decide), if_pos (by decide)]

theorem starJ_03 (β γ : ℝ) : starJ β γ 0 3 = γ := by
  unfold starJ starBond
  rw [if_pos (by decide), if_neg (by decide)]

theorem starJ_04 (β γ : ℝ) : starJ β γ 0 4 = γ := by
  unfold starJ starBond
  rw [if_pos (by decide), if_neg (by decide)]

theorem starJ_10 (β γ : ℝ) : starJ β γ 1 0 = β := by
  unfold starJ starBond
  rw [if_pos (by decide), if_pos (by decide)]

theorem starJ_20 (β γ : ℝ) : starJ β γ 2 0 = β := by
  unfold starJ starBond
  rw [if_pos (by decide), if_pos (by decide)]

theorem starJ_30 (β γ : ℝ) : starJ β γ 3 0 = γ := by
  unfold starJ starBond
  rw [if_pos (by decide), if_neg (by decide)]

theorem starJ_40 (β γ : ℝ) : starJ β γ 4 0 = γ := by
  unfold starJ starBond
  rw [if_pos (by decide), if_neg (by decide)]

/-- Leaf-to-leaf entries vanish: their star distance is two. -/
theorem starJ_leaf (β γ : ℝ) (i j : Fin 5) (h : starDist i j ≠ 1) :
    starJ β γ i j = 0 := by
  unfold starJ
  rw [if_neg h]

/-- The window, as the centre's envelope row sum. -/
theorem starJ_row0 (β γ : ℝ) :
    ∑ j, Real.tanh |starJ β γ 0 j|
      = 2 * Real.tanh |β| + 2 * Real.tanh |γ| := by
  rw [Fin.sum_univ_five, starJ_diag β γ 0, starJ_01 β γ, starJ_02 β γ,
    starJ_03 β γ, starJ_04 β γ, abs_zero, tanh_zero']
  ring

theorem starJ_row1 (β γ : ℝ) :
    ∑ j, Real.tanh |starJ β γ 1 j| = Real.tanh |β| := by
  rw [Fin.sum_univ_five, starJ_10 β γ, starJ_diag β γ 1,
    starJ_leaf β γ 1 2 (by decide), starJ_leaf β γ 1 3 (by decide),
    starJ_leaf β γ 1 4 (by decide), abs_zero, tanh_zero']
  ring

theorem starJ_row2 (β γ : ℝ) :
    ∑ j, Real.tanh |starJ β γ 2 j| = Real.tanh |β| := by
  rw [Fin.sum_univ_five, starJ_20 β γ, starJ_leaf β γ 2 1 (by decide),
    starJ_diag β γ 2, starJ_leaf β γ 2 3 (by decide),
    starJ_leaf β γ 2 4 (by decide), abs_zero, tanh_zero']
  ring

theorem starJ_row3 (β γ : ℝ) :
    ∑ j, Real.tanh |starJ β γ 3 j| = Real.tanh |γ| := by
  rw [Fin.sum_univ_five, starJ_30 β γ, starJ_leaf β γ 3 1 (by decide),
    starJ_leaf β γ 3 2 (by decide), starJ_diag β γ 3,
    starJ_leaf β γ 3 4 (by decide), abs_zero, tanh_zero']
  ring

theorem starJ_row4 (β γ : ℝ) :
    ∑ j, Real.tanh |starJ β γ 4 j| = Real.tanh |γ| := by
  rw [Fin.sum_univ_five, starJ_40 β γ, starJ_leaf β γ 4 1 (by decide),
    starJ_leaf β γ 4 2 (by decide), starJ_leaf β γ 4 3 (by decide),
    starJ_diag β γ 4, abs_zero, tanh_zero']
  ring

/-- Every envelope row sum of the star is at most the window. -/
theorem starJ_row (β γ : ℝ) (i : Fin 5) :
    ∑ j, Real.tanh |starJ β γ i j|
      ≤ 2 * Real.tanh |β| + 2 * Real.tanh |γ| := by
  have hb := tanh_nonneg_of_nonneg (abs_nonneg β)
  have hg := tanh_nonneg_of_nonneg (abs_nonneg γ)
  fin_cases i
  · exact le_of_eq (starJ_row0 β γ)
  · rw [starJ_row1 β γ]
    linarith
  · rw [starJ_row2 β γ]
    linarith
  · rw [starJ_row3 β γ]
    linarith
  · rw [starJ_row4 β γ]
    linarith

/-- **The window of the lane, instantiated.**  The anisotropic star Ising
weight with `2 tanh|β| + 2 tanh|γ| < 1` has exponentially decaying two-point
correlations in the star distance, at the rate the window names. -/
theorem star_covar_two_point (β γ : ℝ)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| < 1)
    (i₀ j₀ : Fin 5) (f g : (Fin 5 → Fin 2) → ℝ)
    (hf : ∀ k, k ≠ i₀ → deltaAt k f = 0)
    (hg : ∀ k, k ≠ j₀ → deltaAt k g = 0) :
    |covar (gibbsMu (isingWeight (starJ β γ))) f g|
      ≤ deltaAt i₀ f
          * ((2 * Real.tanh |β| + 2 * Real.tanh |γ|) ^ (starDist i₀ j₀)
              / (1 - (2 * Real.tanh |β| + 2 * Real.tanh |γ|)))
          * deltaAt j₀ g / 4 :=
  ising_covar_two_point (starJ β γ) (starJ_diag β γ) (starJ_symm β γ)
    (by
      have hb := tanh_nonneg_of_nonneg (abs_nonneg β)
      have hg := tanh_nonneg_of_nonneg (abs_nonneg γ)
      linarith)
    hwin
    (starJ_row β γ)
    starDist starDist_self starDist_triangle (starJ_supp β γ)
    i₀ j₀ f g hf hg

end StarWitness

end Dobrushin

end YangMills.OS
