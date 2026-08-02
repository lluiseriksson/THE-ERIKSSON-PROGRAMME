/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.DobrushinConditional
import YangMills.OS.DobrushinGruss
import YangMills.OS.DobrushinMatrix

/-!
# D-3d/D-3e — the comparison estimate

Charter: `docs/DOBRUSHIN-D3-CHARTER.md`.  Gates J10 of
`scripts/judge_dobrushin_d3.py` and J10q/J11 of
`scripts/judge_dobrushin_d3b.py`, all committed before this file: J10 predicted
the covariance bound with constant one, J10q sharpened the constant to `1/4`
and exhibited the Bernoulli control that forces it, J11 fixed the orientation
of `C` on a cell whose minimal coefficients are not symmetric.

## The statement this module exists for

For a probability weight `μ` on a finite product space, invariant under the
single-site conditionals `p`, whose influence matrix is dominated by `C` with
`C i i = 0` and row sums at most `α < 1`:

    |Cov_μ(f, g)|  ≤  (1/4) · ∑_{i,j} δᵢ(f) · D i j · δⱼ(g),      D = ∑ₙ Cⁿ,

and, composing with D-1, the exponential-decay form with `D i j` replaced by
`α^(dist i j) / (1 - α)`.  No cardinality of the index type appears in either
conclusion; the volume enters only through the finite sums, never through a
constant.

## The route (Dobrushin 1968/1970; Simon, Ch. V — classical, and said so)

Iterate the random-scan average `P = (1/m) ∑ᵢ Eᵢ`.  Each step pays a
conditional Grüss quarter (`DobrushinGruss`) per site; the oscillation vector
of the iterates is transported by the key lemma of D-3c
(`DobrushinConditional`); the accumulated transport is dominated, by a finite
vector induction with no limits, by the partial resolvent sums of the
transpose; and the remainder dies geometrically at rate
`1 - (1-α)/m`.  Every statement up to the final series form is a FINITE
inequality; the single limit is taken at the level of the bound, exactly as
prohibition 2 of the charter demands.

## What this module does NOT claim

The hypotheses (`hinv`, the influence domination) are DISCHARGED here only by
the non-vacuity witness, not for any Gibbs cell of the S block: constructing
the single-site conditionals of `gibbsWeight` and dominating them through the
D-2a envelope is D-4's assembly, and no sentence below pretends otherwise.
Nothing here mentions transfer operators, spectral gaps, or Yang–Mills.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {S : Type*} [Fintype S] [Nonempty S]

/-! ## §1  Expectation under a weight on the configuration space -/

theorem expect_sum_comm {β : Type*} (μ : (ι → S) → ℝ) (s : Finset β)
    (F : β → (ι → S) → ℝ) :
    expect μ (fun η => ∑ b ∈ s, F b η) = ∑ b ∈ s, expect μ (F b) := by
  unfold expect
  calc ∑ η, μ η * ∑ b ∈ s, F b η
      = ∑ η, ∑ b ∈ s, μ η * F b η :=
        Finset.sum_congr rfl fun η _ => by rw [Finset.mul_sum]
    _ = ∑ b ∈ s, ∑ η, μ η * F b η := Finset.sum_comm

theorem expect_div (μ u : (ι → S) → ℝ) (c : ℝ) :
    expect μ (fun η => u η / c) = expect μ u / c := by
  unfold expect
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun η _ => (mul_div_assoc _ _ _).symm

theorem abs_expect_le {μ : (ι → S) → ℝ} (hμ0 : ∀ η, 0 ≤ μ η)
    (hμ1 : ∑ η, μ η = 1) {h : (ι → S) → ℝ} {c : ℝ} (hb : ∀ η, |h η| ≤ c) :
    |expect μ h| ≤ c := by
  unfold expect
  calc |∑ η, μ η * h η|
      ≤ ∑ η, |μ η * h η| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ η, μ η * |h η| := Finset.sum_congr rfl fun η _ => by
        rw [abs_mul, abs_of_nonneg (hμ0 η)]
    _ ≤ ∑ η, μ η * c := Finset.sum_le_sum fun η _ =>
        mul_le_mul_of_nonneg_left (hb η) (hμ0 η)
    _ = c := by rw [← Finset.sum_mul, hμ1, one_mul]

/-! ## §2  Connected correlation, and the global Grüss bound -/

/-- The connected correlation (covariance) of two observables under `μ`. -/
noncomputable def covar (μ f g : (ι → S) → ℝ) : ℝ :=
  expect μ (fun η => f η * g η) - expect μ f * expect μ g

/-- The global Grüss bound on the whole configuration space: the crude estimate
that controls the telescoping remainder. -/
theorem abs_covar_le_osc {μ : (ι → S) → ℝ} (hμ0 : ∀ η, 0 ≤ μ η)
    (hμ1 : ∑ η, μ η = 1) (f g : (ι → S) → ℝ) :
    |covar μ f g| ≤ osc f * osc g / 4 := by
  unfold covar
  exact gruss_covariance_osc_le hμ0 hμ1

/-! ## §3  Oscillation is at most the sum of the single-site oscillations -/

theorem abs_sub_le_sum_deltaAt (f : (ι → S) → ℝ) (η' : ι → S) (A : Finset ι) :
    ∀ η : ι → S, (∀ j, j ∉ A → η j = η' j) →
      |f η - f η'| ≤ ∑ i ∈ A, deltaAt i f := by
  induction A using Finset.cons_induction with
  | empty =>
      intro η h
      have hEq : η = η' := funext fun j => h j (Finset.not_mem_empty j)
      rw [hEq, sub_self, abs_zero]
      exact Finset.sum_nonneg fun i hi => absurd hi (Finset.not_mem_empty i)
  | cons a A' ha ih =>
      intro η h
      set η'' := Function.update η a (η' a) with hdef
      have h1 : |f η - f η''| ≤ deltaAt a f := by
        rw [hdef]
        exact abs_sub_update_le_deltaAt a f η (η' a)
      have h2 : |f η'' - f η'| ≤ ∑ i ∈ A', deltaAt i f := by
        apply ih
        intro j hj
        by_cases hja : j = a
        · rw [hdef, hja]
          exact update_self' η a (η' a)
        · have hjc : j ∉ Finset.cons a A' ha := by
            intro hmem
            rcases Finset.mem_cons.mp hmem with h' | h'
            · exact hja h'
            · exact hj h'
          rw [hdef, update_other _ _ _ hja]
          exact h j hjc
      calc |f η - f η'|
          ≤ |f η - f η''| + |f η'' - f η'| := abs_sub_le _ _ _
        _ ≤ deltaAt a f + ∑ i ∈ A', deltaAt i f := add_le_add h1 h2
        _ = ∑ i ∈ Finset.cons a A' ha, deltaAt i f := by
            rw [Finset.sum_cons]

/-- Changing the configuration one site at a time: the total oscillation is at
most the sum of the single-site oscillations. -/
theorem osc_le_sum_deltaAt (f : (ι → S) → ℝ) :
    osc f ≤ ∑ i, deltaAt i f := by
  refine osc_le_of_pairwise fun η η' => ?_
  calc f η - f η' ≤ |f η - f η'| := le_abs_self _
    _ ≤ ∑ i ∈ Finset.univ, deltaAt i f :=
        abs_sub_le_sum_deltaAt f η' Finset.univ η fun j hj =>
          absurd (Finset.mem_univ j) hj

/-! ## §4  The random scan and its iterates -/

/-- The random-scan operator: the average of the single-site conditionals. -/
noncomputable def scan (p : ι → (ι → S) → S → ℝ) (f : (ι → S) → ℝ) :
    (ι → S) → ℝ :=
  fun η => (∑ i, condExp p i f η) / (Fintype.card ι : ℝ)

/-- Iterates of the random scan. -/
noncomputable def scanIter (p : ι → (ι → S) → S → ℝ) (f : (ι → S) → ℝ) :
    ℕ → (ι → S) → ℝ
  | 0 => f
  | n + 1 => scan p (scanIter p f n)

theorem card_pos_real : (0 : ℝ) < (Fintype.card ι : ℝ) := by
  exact_mod_cast Fintype.card_pos (α := ι)

theorem one_le_card_real : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
  exact_mod_cast Fintype.card_pos (α := ι)

/-- The scan preserves the expectation, provided each conditional does. -/
theorem expect_scan {μ : (ι → S) → ℝ} {p : ι → (ι → S) → S → ℝ}
    (hinv : ∀ (i : ι) (F : (ι → S) → ℝ), expect μ (condExp p i F) = expect μ F)
    (f : (ι → S) → ℝ) : expect μ (scan p f) = expect μ f := by
  unfold scan
  rw [expect_div, expect_sum_comm]
  have hsum : ∑ i : ι, expect μ (condExp p i f)
      = (Fintype.card ι : ℝ) * expect μ f := by
    rw [Finset.sum_congr rfl fun i _ => hinv i f, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [hsum]
  exact mul_div_cancel_left₀ _ (ne_of_gt card_pos_real)

theorem expect_scanIter {μ : (ι → S) → ℝ} {p : ι → (ι → S) → S → ℝ}
    (hinv : ∀ (i : ι) (F : (ι → S) → ℝ), expect μ (condExp p i F) = expect μ F)
    (f : (ι → S) → ℝ) :
    ∀ n, expect μ (scanIter p f n) = expect μ f := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show expect μ (scan p (scanIter p f n)) = expect μ f
      rw [expect_scan hinv, ih]

/-! ## §5  Transport of the oscillation vector -/

/-- One scan step on oscillation vectors:
`(1 - 1/m) v k + (∑ i, C i k · v i)/m`, with `m` the number of sites. -/
noncomputable def scanStep (C : Matrix ι ι ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun k => (1 - 1 / (Fintype.card ι : ℝ)) * v k
    + (∑ i, C i k * v i) / (Fintype.card ι : ℝ)

noncomputable def scanStepIter (C : Matrix ι ι ℝ) (v : ι → ℝ) :
    ℕ → ι → ℝ
  | 0 => v
  | n + 1 => scanStep C (scanStepIter C v n)

theorem one_sub_inv_card_nonneg :
    (0 : ℝ) ≤ 1 - 1 / (Fintype.card ι : ℝ) := by
  have hm := card_pos_real (ι := ι)
  have h1 : 1 / (Fintype.card ι : ℝ) ≤ 1 := by
    rw [div_le_one hm]
    exact one_le_card_real
  linarith

theorem scanStep_nonneg {C : Matrix ι ι ℝ} (hC0 : ∀ i j, 0 ≤ C i j)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) (k : ι) : 0 ≤ scanStep C v k := by
  unfold scanStep
  have h1 := mul_nonneg (one_sub_inv_card_nonneg (ι := ι)) (hv k)
  have h2 : (0 : ℝ) ≤ ∑ i, C i k * v i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hC0 i k) (hv i)
  have h3 := div_nonneg h2 (le_of_lt (card_pos_real (ι := ι)))
  linarith

theorem scanStep_mono {C : Matrix ι ι ℝ} (hC0 : ∀ i j, 0 ≤ C i j)
    {v w : ι → ℝ} (hvw : ∀ i, v i ≤ w i) (k : ι) :
    scanStep C v k ≤ scanStep C w k := by
  unfold scanStep
  have h1 := mul_le_mul_of_nonneg_left (hvw k) (one_sub_inv_card_nonneg (ι := ι))
  have hsum : ∑ i, C i k * v i ≤ ∑ i, C i k * w i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hvw i) (hC0 i k)
  have h2 := div_le_div_of_nonneg_right' hsum (card_pos_real (ι := ι))
  linarith

theorem scanStepIter_nonneg {C : Matrix ι ι ℝ} (hC0 : ∀ i j, 0 ≤ C i j)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    ∀ (n : ℕ) (i : ι), 0 ≤ scanStepIter C v n i := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
      intro i
      simp only [scanStepIter]
      exact scanStep_nonneg hC0 ih i

/-- An influence majorant with zero diagonal is entrywise nonnegative: off the
diagonal it dominates a total variation, and the diagonal is zero by
hypothesis. -/
theorem majorant_nonneg {p : ι → (ι → S) → S → ℝ} {C : Matrix ι ι ℝ}
    (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k) :
    ∀ i j, 0 ≤ C i j := by
  intro i j
  by_cases hji : j = i
  · rw [hji]
    exact le_of_eq (hCdiag i).symm
  · obtain ⟨η⟩ : Nonempty (ι → S) := inferInstance
    exact le_trans (TV_nonneg (p i η) (p i η)) (hC i j hji η η fun _ _ => rfl)

/-- **D-3c applied to the scan**: one scan step transports the oscillation
vector by at most `scanStep C`. -/
theorem deltaAt_scan_le {p : ι → (ι → S) → S → ℝ}
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hloc : KernelLocal p)
    {C : Matrix ι ι ℝ} (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k)
    (f : (ι → S) → ℝ) (k : ι) :
    deltaAt k (scan p f) ≤ scanStep C (fun j => deltaAt j f) k := by
  have hδ : deltaAt k (scan p f)
      ≤ (∑ i, deltaAt k (condExp p i f)) / (Fintype.card ι : ℝ) := by
    unfold scan
    calc deltaAt k (fun η => (∑ i, condExp p i f η) / (Fintype.card ι : ℝ))
        ≤ deltaAt k (fun η => ∑ i, condExp p i f η) / (Fintype.card ι : ℝ) :=
          deltaAt_div_le k _ (le_of_lt (card_pos_real (ι := ι)))
      _ ≤ (∑ i, deltaAt k (condExp p i f)) / (Fintype.card ι : ℝ) :=
          div_le_div_of_nonneg_right'
            (deltaAt_sum_le k Finset.univ fun i => condExp p i f)
            (card_pos_real (ι := ι))
  refine hδ.trans ?_
  show (∑ i, deltaAt k (condExp p i f)) / (Fintype.card ι : ℝ)
      ≤ (1 - 1 / (Fintype.card ι : ℝ)) * deltaAt k f
        + (∑ i, C i k * deltaAt i f) / (Fintype.card ι : ℝ)
  have hterm : ∑ i, deltaAt k (condExp p i f)
      ≤ ∑ i, ((if k = i then 0 else deltaAt k f) + C i k * deltaAt i f) :=
    Finset.sum_le_sum fun i _ =>
      deltaAt_condExp_le_matrix hp0 hp1 hloc C hCdiag hC i k f
  refine (div_le_div_of_nonneg_right' hterm (card_pos_real (ι := ι))).trans ?_
  have hcount : ∑ i, (if k = i then (0 : ℝ) else deltaAt k f)
      = ((Fintype.card ι : ℝ) - 1) * deltaAt k f := by
    have hpt : ∀ i ∈ (Finset.univ : Finset ι),
        (if k = i then (0 : ℝ) else deltaAt k f)
          = deltaAt k f - (if k = i then deltaAt k f else 0) := by
      intro i _
      by_cases hik : k = i
      · rw [if_pos hik, if_pos hik]
        ring
      · rw [if_neg hik, if_neg hik]
        ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq Finset.univ k fun _ => deltaAt k f,
      if_pos (Finset.mem_univ k)]
    ring
  rw [Finset.sum_add_distrib, hcount, add_div]
  have hne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt (card_pos_real (ι := ι))
  have heq : ((Fintype.card ι : ℝ) - 1) * deltaAt k f / (Fintype.card ι : ℝ)
      = (1 - 1 / (Fintype.card ι : ℝ)) * deltaAt k f := by
    have h1 : ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)
        = 1 - 1 / (Fintype.card ι : ℝ) := by
      rw [sub_div, div_self hne]
    calc ((Fintype.card ι : ℝ) - 1) * deltaAt k f / (Fintype.card ι : ℝ)
        = (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) * deltaAt k f := by
          ring
      _ = (1 - 1 / (Fintype.card ι : ℝ)) * deltaAt k f := by rw [h1]
  exact le_of_eq (by rw [heq])

/-- Iterated transport: `δ(Pⁿ f) ≤ (scanStep)ⁿ (δ f)` coordinatewise. -/
theorem deltaAt_scanIter_le {p : ι → (ι → S) → S → ℝ}
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hloc : KernelLocal p)
    {C : Matrix ι ι ℝ} (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k)
    (f : (ι → S) → ℝ) :
    ∀ (n : ℕ) (k : ι), deltaAt k (scanIter p f n)
      ≤ scanStepIter C (fun j => deltaAt j f) n k := by
  have hC0 := majorant_nonneg hCdiag hC
  intro n
  induction n with
  | zero =>
      intro k
      exact le_refl _
  | succ n ih =>
      intro k
      simp only [scanIter, scanStepIter]
      calc deltaAt k (scan p (scanIter p f n))
          ≤ scanStep C (fun j => deltaAt j (scanIter p f n)) k :=
            deltaAt_scan_le hp0 hp1 hloc hCdiag hC _ k
        _ ≤ scanStep C (scanStepIter C (fun j => deltaAt j f) n) k :=
            scanStep_mono hC0 (fun i => ih i) k

/-! ## §6  The ℓ¹ contraction of the transport -/

theorem gamma_nonneg {α : ℝ} (hα0 : 0 ≤ α) :
    (0 : ℝ) ≤ 1 - (1 - α) / (Fintype.card ι : ℝ) := by
  have hm := card_pos_real (ι := ι)
  have hm1 := one_le_card_real (ι := ι)
  rw [sub_nonneg, div_le_one hm]
  linarith

theorem gamma_lt_one {α : ℝ} (hα1 : α < 1) :
    1 - (1 - α) / (Fintype.card ι : ℝ) < 1 := by
  have hm := card_pos_real (ι := ι)
  have h : 0 < (1 - α) / (Fintype.card ι : ℝ) := div_pos (by linarith) hm
  linarith

theorem sum_scanStep_le {C : Matrix ι ι ℝ} (hC0 : ∀ i j, 0 ≤ C i j)
    {α : ℝ} (hrow : ∀ i, ∑ k, C i k ≤ α)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    ∑ k, scanStep C v k
      ≤ (1 - (1 - α) / (Fintype.card ι : ℝ)) * ∑ k, v k := by
  unfold scanStep
  have hm := card_pos_real (ι := ι)
  rw [Finset.sum_add_distrib]
  have h1 : ∑ k, (1 - 1 / (Fintype.card ι : ℝ)) * v k
      = (1 - 1 / (Fintype.card ι : ℝ)) * ∑ k, v k := by
    rw [Finset.mul_sum]
  have h2 : ∑ k, (∑ i, C i k * v i) / (Fintype.card ι : ℝ)
      ≤ (α / (Fintype.card ι : ℝ)) * ∑ k, v k := by
    rw [← Finset.sum_div]
    have hswap : ∑ k, ∑ i, C i k * v i = ∑ i, ∑ k, C i k * v i :=
      Finset.sum_comm
    have hfin : ∑ i, ∑ k, C i k * v i ≤ α * ∑ k, v k := by
      calc ∑ i, ∑ k, C i k * v i
          = ∑ i, (∑ k, C i k) * v i :=
            Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
        _ ≤ ∑ i, α * v i :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right (hrow i) (hv i)
        _ = α * ∑ i, v i := by rw [Finset.mul_sum]
    calc (∑ k, ∑ i, C i k * v i) / (Fintype.card ι : ℝ)
        ≤ (α * ∑ k, v k) / (Fintype.card ι : ℝ) := by
          rw [hswap]
          exact div_le_div_of_nonneg_right' hfin hm
      _ = (α / (Fintype.card ι : ℝ)) * ∑ k, v k := by ring
  rw [h1]
  have hΣv : (0 : ℝ) ≤ ∑ k, v k := Finset.sum_nonneg fun k _ => hv k
  calc (1 - 1 / (Fintype.card ι : ℝ)) * (∑ k, v k)
        + ∑ k, (∑ i, C i k * v i) / (Fintype.card ι : ℝ)
      ≤ (1 - 1 / (Fintype.card ι : ℝ)) * (∑ k, v k)
        + (α / (Fintype.card ι : ℝ)) * ∑ k, v k := by linarith [h2]
    _ = (1 - (1 - α) / (Fintype.card ι : ℝ)) * ∑ k, v k := by ring

theorem sum_scanStepIter_le {C : Matrix ι ι ℝ} (hC0 : ∀ i j, 0 ≤ C i j)
    {α : ℝ} (hα0 : 0 ≤ α) (hrow : ∀ i, ∑ k, C i k ≤ α)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    ∀ n : ℕ, ∑ k, scanStepIter C v n k
      ≤ (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ n * ∑ k, v k := by
  intro n
  induction n with
  | zero =>
      simp only [scanStepIter, pow_zero, one_mul]
      exact le_refl _
  | succ n ih =>
      simp only [scanStepIter]
      have hγ0 := gamma_nonneg (ι := ι) hα0
      calc ∑ k, scanStep C (scanStepIter C v n) k
          ≤ (1 - (1 - α) / (Fintype.card ι : ℝ))
              * ∑ k, scanStepIter C v n k :=
            sum_scanStep_le hC0 hrow (scanStepIter_nonneg hC0 hv n)
        _ ≤ (1 - (1 - α) / (Fintype.card ι : ℝ))
              * ((1 - (1 - α) / (Fintype.card ι : ℝ)) ^ n * ∑ k, v k) :=
            mul_le_mul_of_nonneg_left ih hγ0
        _ = (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ (n + 1) * ∑ k, v k := by
            ring

/-! ## §7  The accumulated transport against the partial resolvent -/

/-- The accumulated transport `∑_{n<N} (scanStep)ⁿ v`. -/
noncomputable def transportSum (C : Matrix ι ι ℝ) (v : ι → ℝ) (N : ℕ) :
    ι → ℝ :=
  fun k => ∑ n ∈ Finset.range N, scanStepIter C v n k

/-- The partial resolvent of the transpose, `∑_{n<N} (Cᵀ)ⁿ v`, defined by the
recursion it satisfies. -/
noncomputable def seriesPartial (C : Matrix ι ι ℝ) (v : ι → ℝ) :
    ℕ → ι → ℝ
  | 0 => fun _ => 0
  | N + 1 => fun k => v k + ∑ i, C i k * seriesPartial C v N i

theorem seriesPartial_nonneg {C : Matrix ι ι ℝ} (hC0 : ∀ i j, 0 ≤ C i j)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    ∀ (N : ℕ) (k : ι), 0 ≤ seriesPartial C v N k := by
  intro N
  induction N with
  | zero => intro k; exact le_refl 0
  | succ N ih =>
      intro k
      simp only [seriesPartial]
      have h1 : (0 : ℝ) ≤ ∑ i, C i k * seriesPartial C v N i :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hC0 i k) (ih i)
      linarith [hv k]

theorem seriesPartial_le_succ {C : Matrix ι ι ℝ} (hC0 : ∀ i j, 0 ≤ C i j)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    ∀ (N : ℕ) (k : ι), seriesPartial C v N k ≤ seriesPartial C v (N + 1) k := by
  intro N
  induction N with
  | zero =>
      intro k
      exact seriesPartial_nonneg hC0 hv 1 k
  | succ N ih =>
      intro k
      simp only [seriesPartial]
      have h1 : ∑ i, C i k * seriesPartial C v N i
          ≤ ∑ i, C i k * seriesPartial C v (N + 1) i :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (ih i) (hC0 i k)
      linarith

/-- Linearity of the scan step over finite sums of vectors. -/
theorem scanStep_sum {β : Type*} (C : Matrix ι ι ℝ) (s : Finset β)
    (W : β → ι → ℝ) (k : ι) :
    scanStep C (fun i => ∑ b ∈ s, W b i) k = ∑ b ∈ s, scanStep C (W b) k := by
  unfold scanStep
  rw [Finset.mul_sum]
  have hswap : ∑ i, C i k * ∑ b ∈ s, W b i
      = ∑ b ∈ s, ∑ i, C i k * W b i := by
    calc ∑ i, C i k * ∑ b ∈ s, W b i
        = ∑ i, ∑ b ∈ s, C i k * W b i :=
          Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ = ∑ b ∈ s, ∑ i, C i k * W b i := Finset.sum_comm
  rw [hswap, Finset.sum_div, ← Finset.sum_add_distrib]

/-- Scalar homogeneity of the scan step. -/
theorem scanStep_const_mul (C : Matrix ι ι ℝ) (c : ℝ) (w : ι → ℝ) (k : ι) :
    scanStep C (fun i => c * w i) k = c * scanStep C w k := by
  unfold scanStep
  have h : ∑ i, C i k * (c * w i) = c * ∑ i, C i k * w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]
  ring

/-- **The finite vector induction** — the accumulated transport is dominated by
`m` times the partial resolvent of the transpose.  No limit is taken; the
inequality holds for every `N` by induction alone. -/
theorem transportSum_le {C : Matrix ι ι ℝ} (hC0 : ∀ i j, 0 ≤ C i j)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    ∀ (N : ℕ) (k : ι), transportSum C v N k
      ≤ (Fintype.card ι : ℝ) * seriesPartial C v N k := by
  intro N
  induction N with
  | zero =>
      intro k
      simp only [transportSum, Finset.range_zero, Finset.sum_empty,
        seriesPartial, mul_zero]
      exact le_refl 0
  | succ N ih =>
      intro k
      have hne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt (card_pos_real (ι := ι))
      have hstep : transportSum C v (N + 1) k
          = v k + ∑ n ∈ Finset.range N, scanStep C (scanStepIter C v n) k := by
        unfold transportSum
        rw [Finset.sum_range_succ']
        simp only [scanStepIter]
        rw [add_comm]
      have hlin : ∑ n ∈ Finset.range N, scanStep C (scanStepIter C v n) k
          = scanStep C (transportSum C v N) k := by
        unfold transportSum
        exact (scanStep_sum C (Finset.range N) (fun n => scanStepIter C v n) k).symm
      have hexp : (Fintype.card ι : ℝ) * scanStep C (seriesPartial C v N) k
          = ((Fintype.card ι : ℝ) - 1) * seriesPartial C v N k
            + ∑ i, C i k * seriesPartial C v N i := by
        have hcancel : (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card ι : ℝ))
            = (Fintype.card ι : ℝ) - 1 := by
          rw [mul_sub, mul_one, mul_one_div, div_self hne]
        unfold scanStep
        rw [mul_add, ← mul_assoc, hcancel, ← mul_div_assoc,
          mul_div_cancel_left₀ _ hne]
      have hmono := seriesPartial_le_succ hC0 hv N k
      have hm1 := one_le_card_real (ι := ι)
      have hmul := scanStep_mono hC0 ih k
      have hcm := scanStep_const_mul C (Fintype.card ι : ℝ)
        (seriesPartial C v N) k
      rw [hcm] at hmul
      have hfin : seriesPartial C v (N + 1) k
          = v k + ∑ i, C i k * seriesPartial C v N i := by
        simp only [seriesPartial]
      have hlast := mul_le_mul_of_nonneg_left hmono
        (by linarith : (0 : ℝ) ≤ (Fintype.card ι : ℝ) - 1)
      calc transportSum C v (N + 1) k
          = v k + scanStep C (transportSum C v N) k := by rw [hstep, hlin]
        _ ≤ v k + (Fintype.card ι : ℝ) * scanStep C (seriesPartial C v N) k := by
            linarith [hmul]
        _ = v k + (((Fintype.card ι : ℝ) - 1) * seriesPartial C v N k
              + ∑ i, C i k * seriesPartial C v N i) := by rw [hexp]
        _ ≤ v k + (((Fintype.card ι : ℝ) - 1) * seriesPartial C v (N + 1) k
              + ∑ i, C i k * seriesPartial C v N i) := by linarith [hlast]
        _ = seriesPartial C v (N + 1) k
              + ((Fintype.card ι : ℝ) - 1) * seriesPartial C v (N + 1) k := by
            rw [hfin]
            ring
        _ = (Fintype.card ι : ℝ) * seriesPartial C v (N + 1) k := by ring

/-- The partial resolvent of the transpose, written through matrix powers:
`(seriesPartial C v N) k = ∑_{n<N} ∑_j (Cⁿ) j k · v j`. -/
theorem seriesPartial_eq_pow_sum (C : Matrix ι ι ℝ) (v : ι → ℝ) :
    ∀ (N : ℕ) (k : ι), seriesPartial C v N k
      = ∑ n ∈ Finset.range N, ∑ j, ((C ^ n) j k) * v j := by
  intro N
  induction N with
  | zero =>
      intro k
      simp only [seriesPartial, Finset.range_zero, Finset.sum_empty]
  | succ N ih =>
      intro k
      simp only [seriesPartial]
      have h0 : ∑ j, ((C ^ 0) j k) * v j = v k := by
        simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have hstepn : ∀ n, ∑ j, ((C ^ (n + 1)) j k) * v j
          = ∑ i, C i k * ∑ j, ((C ^ n) j i) * v j := by
        intro n
        calc ∑ j, ((C ^ (n + 1)) j k) * v j
            = ∑ j, (∑ i, (C ^ n) j i * C i k) * v j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [pow_succ, Matrix.mul_apply]
          _ = ∑ j, ∑ i, (C ^ n) j i * C i k * v j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul]
          _ = ∑ i, ∑ j, (C ^ n) j i * C i k * v j := Finset.sum_comm
          _ = ∑ i, C i k * ∑ j, ((C ^ n) j i) * v j := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
      have hIH : ∑ i, C i k * seriesPartial C v N i
          = ∑ i, C i k * ∑ n ∈ Finset.range N, ∑ j, ((C ^ n) j i) * v j :=
        Finset.sum_congr rfl fun i _ => by rw [ih i]
      rw [hIH]
      have hpush : ∑ i, C i k * ∑ n ∈ Finset.range N, ∑ j, ((C ^ n) j i) * v j
          = ∑ n ∈ Finset.range N, ∑ i, C i k * ∑ j, ((C ^ n) j i) * v j := by
        calc ∑ i, C i k * ∑ n ∈ Finset.range N, ∑ j, ((C ^ n) j i) * v j
            = ∑ i, ∑ n ∈ Finset.range N,
                C i k * ∑ j, ((C ^ n) j i) * v j :=
              Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
          _ = ∑ n ∈ Finset.range N, ∑ i,
                C i k * ∑ j, ((C ^ n) j i) * v j := Finset.sum_comm
      rw [hpush,
        Finset.sum_congr rfl fun n (_ : n ∈ Finset.range N) => (hstepn n).symm,
        Finset.sum_range_succ', h0]
      ring

/-! ## §8  The one-step conditional Grüss bound -/

/-- **The one-step bound**: testing `g` against the defect of one conditioning
pays at most a quarter of the product of the two oscillations at that site.
The pointwise identity behind it: `Eᵢ(g·(f - Eᵢ f))(η)` IS the covariance of
the two sections under `p i η`. -/
theorem abs_expect_mul_sub_condExp_le {μ : (ι → S) → ℝ}
    {p : ι → (ι → S) → S → ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hloc : KernelLocal p)
    (hinv : ∀ (i : ι) (F : (ι → S) → ℝ), expect μ (condExp p i F) = expect μ F)
    (i : ι) (f g : (ι → S) → ℝ) :
    |expect μ (fun η => g η * (f η - condExp p i f η))|
      ≤ deltaAt i g * deltaAt i f / 4 := by
  rw [← hinv i (fun η => g η * (f η - condExp p i f η))]
  refine abs_expect_le hμ0 hμ1 fun η => ?_
  -- the outer conditional, unfolded by definitional equality
  have hout : condExp p i (fun ξ => g ξ * (f ξ - condExp p i f ξ)) η
      = ∑ s, p i η s * (g (Function.update η i s)
          * (f (Function.update η i s)
            - condExp p i f (Function.update η i s))) := rfl
  -- the inner conditional does not move along the section (locality)
  have hA : ∀ s : S, condExp p i f (Function.update η i s) = condExp p i f η :=
    fun s => condExp_update_self hloc i f η s
  have hAe : condExp p i f η
      = expect (p i η) (fun t => f (Function.update η i t)) := rfl
  -- the pointwise identity: the conditional of the defect IS a covariance
  have hid : condExp p i (fun ξ => g ξ * (f ξ - condExp p i f ξ)) η
      = expect (p i η)
          (fun s => g (Function.update η i s) * f (Function.update η i s))
        - expect (p i η) (fun s => g (Function.update η i s))
          * expect (p i η) (fun s => f (Function.update η i s)) := by
    rw [hout]
    have hstep : ∀ s : S, p i η s * (g (Function.update η i s)
          * (f (Function.update η i s)
            - condExp p i f (Function.update η i s)))
        = p i η s * (g (Function.update η i s) * f (Function.update η i s))
          - (p i η s * g (Function.update η i s))
            * ∑ t, p i η t * f (Function.update η i t) := by
      intro s
      rw [hA s, hAe]
      unfold expect
      ring
    rw [Finset.sum_congr rfl fun s _ => hstep s]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    unfold expect
  rw [hid]
  have hgr := gruss_covariance_osc_le (p := p i η)
    (f := fun s => g (Function.update η i s))
    (g := fun s => f (Function.update η i s))
    (fun s => hp0 i η s) (hp1 i η)
  refine hgr.trans ?_
  have h1 : osc (fun s => g (Function.update η i s)) ≤ deltaAt i g :=
    osc_section_le_deltaAt i g η
  have h2 : osc (fun s => f (Function.update η i s)) ≤ deltaAt i f :=
    osc_section_le_deltaAt i f η
  have h3 : (0 : ℝ) ≤ osc (fun s => f (Function.update η i s)) :=
    osc_nonneg _
  have h4 : (0 : ℝ) ≤ deltaAt i g := deltaAt_nonneg i g
  exact div_le_div_of_nonneg_right' (mul_le_mul h1 h2 h3 h4)
    (by norm_num : (0 : ℝ) < 4)

/-! ## §9  The telescoping step -/

/-- One telescoping step: the covariance moves by at most an averaged quarter
of the site-by-site oscillation products. -/
theorem covar_scan_step {μ : (ι → S) → ℝ} {p : ι → (ι → S) → S → ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hloc : KernelLocal p)
    (hinv : ∀ (i : ι) (F : (ι → S) → ℝ), expect μ (condExp p i F) = expect μ F)
    (h g : (ι → S) → ℝ) :
    |covar μ h g - covar μ (scan p h) g|
      ≤ (∑ i, deltaAt i g * deltaAt i h) / (4 * (Fintype.card ι : ℝ)) := by
  have hm : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt (card_pos_real (ι := ι))
  have hEs : expect μ (scan p h) = expect μ h := expect_scan hinv h
  have hidt : covar μ h g - covar μ (scan p h) g
      = expect μ (fun η => g η * (h η - scan p h η)) := by
    unfold covar
    rw [hEs]
    have hlin : expect μ (fun η => g η * (h η - scan p h η))
        = expect μ (fun η => h η * g η)
          - expect μ (fun η => scan p h η * g η) := by
      unfold expect
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun η _ => by ring
    rw [hlin]
    ring
  have hnum : ∀ η, ∑ i, g η * (h η - condExp p i h η)
      = (Fintype.card ι : ℝ) * (g η * h η)
        - g η * ∑ i, condExp p i h η := by
    intro η
    calc ∑ i, g η * (h η - condExp p i h η)
        = ∑ i, (g η * h η - g η * condExp p i h η) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ _i : ι, g η * h η) - ∑ i, g η * condExp p i h η :=
          Finset.sum_sub_distrib
      _ = (Fintype.card ι : ℝ) * (g η * h η)
            - g η * ∑ i, condExp p i h η := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.mul_sum]
  have hdec : ∀ η, g η * (h η - scan p h η)
      = (∑ i, g η * (h η - condExp p i h η)) / (Fintype.card ι : ℝ) := by
    intro η
    unfold scan
    rw [hnum η, sub_div, mul_div_cancel_left₀ _ hm, mul_sub, mul_div_assoc]
  rw [hidt]
  have hpt : expect μ (fun η => g η * (h η - scan p h η))
      = expect μ (fun η =>
          (∑ i, g η * (h η - condExp p i h η)) / (Fintype.card ι : ℝ)) := by
    unfold expect
    exact Finset.sum_congr rfl fun η _ => by rw [hdec η]
  rw [hpt, expect_div, expect_sum_comm]
  calc |(∑ i, expect μ (fun η => g η * (h η - condExp p i h η)))
        / (Fintype.card ι : ℝ)|
      = |∑ i, expect μ (fun η => g η * (h η - condExp p i h η))|
          / (Fintype.card ι : ℝ) := by
        rw [abs_div, abs_of_pos (card_pos_real (ι := ι))]
    _ ≤ (∑ i, |expect μ (fun η => g η * (h η - condExp p i h η))|)
          / (Fintype.card ι : ℝ) :=
        div_le_div_of_nonneg_right' (Finset.abs_sum_le_sum_abs _ _)
          (card_pos_real (ι := ι))
    _ ≤ (∑ i, deltaAt i g * deltaAt i h / 4) / (Fintype.card ι : ℝ) :=
        div_le_div_of_nonneg_right'
          (Finset.sum_le_sum fun i _ =>
            abs_expect_mul_sub_condExp_le hμ0 hμ1 hp0 hp1 hloc hinv i h g)
          (card_pos_real (ι := ι))
    _ = (∑ i, deltaAt i g * deltaAt i h) / (4 * (Fintype.card ι : ℝ)) := by
        rw [← Finset.sum_div, div_div]

/-! ## §10  The master bound, finite form -/

/-- **D-3e, finite form.**  For every number of scan steps `N`, the covariance
is controlled by the partial resolvent sums plus a geometrically dying
remainder.  Everything here is a finite sum; no limit has been taken. -/
theorem covar_le_resolvent_partial {μ : (ι → S) → ℝ}
    {p : ι → (ι → S) → S → ℝ} {C : Matrix ι ι ℝ} {α : ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hloc : KernelLocal p)
    (hinv : ∀ (i : ι) (F : (ι → S) → ℝ), expect μ (condExp p i F) = expect μ F)
    (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k)
    (hα0 : 0 ≤ α) (hrow : ∀ i, ∑ k, C i k ≤ α)
    (f g : (ι → S) → ℝ) (N : ℕ) :
    |covar μ f g|
      ≤ (∑ i, ∑ j, deltaAt i f
            * (∑ n ∈ Finset.range N, (C ^ n) i j) * deltaAt j g) / 4
        + osc g * ((1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N
            * ∑ i, deltaAt i f) / 4 := by
  have hC0 := majorant_nonneg hCdiag hC
  have hδf0 : ∀ j, 0 ≤ deltaAt j f := fun j => deltaAt_nonneg j f
  -- telescoping identity
  have htel : ∀ N' : ℕ, covar μ f g
      = (∑ n ∈ Finset.range N',
          (covar μ (scanIter p f n) g - covar μ (scanIter p f (n + 1)) g))
        + covar μ (scanIter p f N') g := by
    intro N'
    induction N' with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, scanIter, zero_add]
    | succ N' ih =>
        rw [Finset.sum_range_succ]
        linarith [ih]
  -- each step
  have hstepbd : ∀ n : ℕ,
      |covar μ (scanIter p f n) g - covar μ (scanIter p f (n + 1)) g|
        ≤ (∑ i, deltaAt i g * deltaAt i (scanIter p f n))
            / (4 * (Fintype.card ι : ℝ)) := by
    intro n
    have h := covar_scan_step hμ0 hμ1 hp0 hp1 hloc hinv (scanIter p f n) g
    simp only [scanIter]
    exact h
  have hdelta := deltaAt_scanIter_le hp0 hp1 hloc hCdiag hC f
  have hstepbd2 : ∀ n : ℕ,
      (∑ i, deltaAt i g * deltaAt i (scanIter p f n))
          / (4 * (Fintype.card ι : ℝ))
        ≤ (∑ i, deltaAt i g * scanStepIter C (fun j => deltaAt j f) n i)
            / (4 * (Fintype.card ι : ℝ)) := fun n =>
    div_le_div_of_nonneg_right'
      (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hdelta n i) (deltaAt_nonneg i g))
      (mul_pos (by norm_num) (card_pos_real (ι := ι)))
  -- sum of the transported steps
  have hsumsteps : ∑ n ∈ Finset.range N,
        (∑ i, deltaAt i g * scanStepIter C (fun j => deltaAt j f) n i)
          / (4 * (Fintype.card ι : ℝ))
      = (∑ i, deltaAt i g * transportSum C (fun j => deltaAt j f) N i)
          / (4 * (Fintype.card ι : ℝ)) := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold transportSum
    rw [Finset.mul_sum]
  -- transport dominated by the partial resolvent
  have hAle : ∑ i, deltaAt i g * transportSum C (fun j => deltaAt j f) N i
      ≤ (Fintype.card ι : ℝ)
        * ∑ i, deltaAt i g * seriesPartial C (fun j => deltaAt j f) N i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc deltaAt i g * transportSum C (fun j => deltaAt j f) N i
        ≤ deltaAt i g * ((Fintype.card ι : ℝ)
            * seriesPartial C (fun j => deltaAt j f) N i) :=
          mul_le_mul_of_nonneg_left (transportSum_le hC0 hδf0 N i)
            (deltaAt_nonneg i g)
      _ = (Fintype.card ι : ℝ)
            * (deltaAt i g * seriesPartial C (fun j => deltaAt j f) N i) := by
          ring
  have hmain : (∑ i, deltaAt i g * transportSum C (fun j => deltaAt j f) N i)
        / (4 * (Fintype.card ι : ℝ))
      ≤ (∑ i, deltaAt i g * seriesPartial C (fun j => deltaAt j f) N i) / 4 := by
    have hm := card_pos_real (ι := ι)
    have hcancel : ((Fintype.card ι : ℝ)
          * ∑ i, deltaAt i g * seriesPartial C (fun j => deltaAt j f) N i)
        / (4 * (Fintype.card ι : ℝ))
        = (∑ i, deltaAt i g * seriesPartial C (fun j => deltaAt j f) N i) / 4 := by
      rw [mul_comm (4 : ℝ) (Fintype.card ι : ℝ), ← div_div,
        mul_div_cancel_left₀ _ (ne_of_gt hm)]
    calc (∑ i, deltaAt i g * transportSum C (fun j => deltaAt j f) N i)
          / (4 * (Fintype.card ι : ℝ))
        ≤ ((Fintype.card ι : ℝ)
            * ∑ i, deltaAt i g * seriesPartial C (fun j => deltaAt j f) N i)
          / (4 * (Fintype.card ι : ℝ)) :=
          div_le_div_of_nonneg_right' hAle
            (mul_pos (by norm_num) hm)
      _ = (∑ i, deltaAt i g
            * seriesPartial C (fun j => deltaAt j f) N i) / 4 := hcancel
  -- the partial resolvent in matrix-power form
  have hform : ∑ i, deltaAt i g * seriesPartial C (fun j => deltaAt j f) N i
      = ∑ i, ∑ j, deltaAt i f
          * (∑ n ∈ Finset.range N, (C ^ n) i j) * deltaAt j g := by
    have hswap : ∀ k, seriesPartial C (fun j => deltaAt j f) N k
        = ∑ j, (∑ n ∈ Finset.range N, (C ^ n) j k) * deltaAt j f := by
      intro k
      rw [seriesPartial_eq_pow_sum, Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    calc ∑ k, deltaAt k g * seriesPartial C (fun j => deltaAt j f) N k
        = ∑ k, ∑ j, deltaAt k g
            * ((∑ n ∈ Finset.range N, (C ^ n) j k) * deltaAt j f) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hswap k, Finset.mul_sum]
      _ = ∑ j, ∑ k, deltaAt k g
            * ((∑ n ∈ Finset.range N, (C ^ n) j k) * deltaAt j f) :=
          Finset.sum_comm
      _ = ∑ i, ∑ j, deltaAt i f
            * (∑ n ∈ Finset.range N, (C ^ n) i j) * deltaAt j g := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact Finset.sum_congr rfl fun k _ => by ring
  -- the remainder
  have hrem : |covar μ (scanIter p f N) g|
      ≤ osc g * ((1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N
          * ∑ i, deltaAt i f) / 4 := by
    have hosc1 : osc (scanIter p f N) ≤ ∑ i, deltaAt i (scanIter p f N) :=
      osc_le_sum_deltaAt _
    have hosc2 : ∑ i, deltaAt i (scanIter p f N)
        ≤ ∑ i, scanStepIter C (fun j => deltaAt j f) N i :=
      Finset.sum_le_sum fun i _ => hdelta N i
    have hosc3 : ∑ i, scanStepIter C (fun j => deltaAt j f) N i
        ≤ (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N * ∑ i, deltaAt i f :=
      sum_scanStepIter_le hC0 hα0 hrow hδf0 N
    have hg0 : (0 : ℝ) ≤ osc g := osc_nonneg g
    calc |covar μ (scanIter p f N) g|
        ≤ osc (scanIter p f N) * osc g / 4 := abs_covar_le_osc hμ0 hμ1 _ g
      _ ≤ ((1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N * ∑ i, deltaAt i f)
            * osc g / 4 :=
          div_le_div_of_nonneg_right'
            (mul_le_mul_of_nonneg_right (by linarith) hg0)
            (by norm_num)
      _ = osc g * ((1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N
            * ∑ i, deltaAt i f) / 4 := by ring
  -- assemble
  calc |covar μ f g|
      = |(∑ n ∈ Finset.range N,
            (covar μ (scanIter p f n) g - covar μ (scanIter p f (n + 1)) g))
          + covar μ (scanIter p f N) g| := by rw [← htel N]
    _ ≤ |∑ n ∈ Finset.range N,
            (covar μ (scanIter p f n) g - covar μ (scanIter p f (n + 1)) g)|
          + |covar μ (scanIter p f N) g| := abs_add _ _
    _ ≤ (∑ n ∈ Finset.range N,
            |covar μ (scanIter p f n) g - covar μ (scanIter p f (n + 1)) g|)
          + |covar μ (scanIter p f N) g| := by
        have := Finset.abs_sum_le_sum_abs
          (fun n => covar μ (scanIter p f n) g
            - covar μ (scanIter p f (n + 1)) g) (Finset.range N)
        linarith
    _ ≤ (∑ n ∈ Finset.range N,
            (∑ i, deltaAt i g * scanStepIter C (fun j => deltaAt j f) n i)
              / (4 * (Fintype.card ι : ℝ)))
          + |covar μ (scanIter p f N) g| := by
        have hsum := Finset.sum_le_sum
          (fun n (_ : n ∈ Finset.range N) => (hstepbd n).trans (hstepbd2 n))
        linarith
    _ ≤ (∑ i, ∑ j, deltaAt i f
            * (∑ n ∈ Finset.range N, (C ^ n) i j) * deltaAt j g) / 4
          + osc g * ((1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N
              * ∑ i, deltaAt i f) / 4 := by
        rw [hsumsteps]
        have h1 := hmain
        rw [hform] at h1
        linarith [hrem, h1]

/-! ## §11  The registered target — series form, and the decay corollaries -/

/-- **D-3e, the comparison estimate.**  The registered target of the charter,
with the quarter constant of J10q and the orientation of J11:

    |Cov_μ(f,g)| ≤ (1/4) ∑_{i,j} δᵢ(f) · (∑ₙ (Cⁿ)ᵢⱼ) · δⱼ(g).

The single limit of the campaign is taken here, at the level of the bound. -/
theorem covar_le_resolvent_tsum {μ : (ι → S) → ℝ}
    {p : ι → (ι → S) → S → ℝ} {C : Matrix ι ι ℝ} {α : ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hloc : KernelLocal p)
    (hinv : ∀ (i : ι) (F : (ι → S) → ℝ), expect μ (condExp p i F) = expect μ F)
    (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hrow : ∀ i, ∑ k, C i k ≤ α)
    (f g : (ι → S) → ℝ) :
    |covar μ f g|
      ≤ (∑ i, ∑ j, deltaAt i f * (∑' n : ℕ, (C ^ n) i j) * deltaAt j g) / 4 := by
  have hC0 := majorant_nonneg hCdiag hC
  have hsummable : ∀ i j, Summable fun n : ℕ => (C ^ n) i j := fun i j =>
    Summable.of_nonneg_of_le (fun n => Matrix.pow_apply_nonneg hC0 n i j)
      (fun n => Matrix.pow_apply_le hC0 hα0 hrow n i j)
      (summable_geometric_of_lt_one hα0 hα1)
  have hpartial : ∀ (N : ℕ) (i j : ι),
      ∑ n ∈ Finset.range N, (C ^ n) i j ≤ ∑' n : ℕ, (C ^ n) i j := fun N i j =>
    Summable.sum_le_tsum (Finset.range N)
      (fun n _ => Matrix.pow_apply_nonneg hC0 n i j) (hsummable i j)
  set A := (∑ i, ∑ j, deltaAt i f * (∑' n : ℕ, (C ^ n) i j) * deltaAt j g) / 4
    with hAdef
  have hbound : ∀ N : ℕ, |covar μ f g|
      ≤ A + osc g * ((1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N
          * ∑ i, deltaAt i f) / 4 := by
    intro N
    have h := covar_le_resolvent_partial hμ0 hμ1 hp0 hp1 hloc hinv hCdiag hC
      hα0 hrow f g N
    have hmono : (∑ i, ∑ j, deltaAt i f
          * (∑ n ∈ Finset.range N, (C ^ n) i j) * deltaAt j g) / 4 ≤ A := by
      rw [hAdef]
      refine div_le_div_of_nonneg_right' ?_ (by norm_num)
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (deltaAt_nonneg j g)
      exact mul_le_mul_of_nonneg_left (hpartial N i j) (deltaAt_nonneg i f)
    linarith
  have hγ0 := gamma_nonneg (ι := ι) hα0
  have hγ1 := gamma_lt_one (ι := ι) hα1
  have hlim : Filter.Tendsto
      (fun N : ℕ => A + (osc g * (∑ i, deltaAt i f) / 4)
        * (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N)
      Filter.atTop (nhds A) := by
    have h1 : Filter.Tendsto
        (fun N : ℕ => (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1
    have h2 := h1.const_mul (osc g * (∑ i, deltaAt i f) / 4)
    have h3 := h2.const_add A
    simpa using h3
  refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun N => ?_)
  calc |covar μ f g|
      ≤ A + osc g * ((1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N
          * ∑ i, deltaAt i f) / 4 := hbound N
    _ = A + (osc g * (∑ i, deltaAt i f) / 4)
          * (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N := by ring

/-- **The sentence D-3 exists for** — composing the comparison estimate with
D-1: exponential decay of connected correlations, at a rate read off the
single-site data, with no cardinality of the index type anywhere. -/
theorem covar_exp_decay {μ : (ι → S) → ℝ}
    {p : ι → (ι → S) → S → ℝ} {C : Matrix ι ι ℝ} {α : ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hloc : KernelLocal p)
    (hinv : ∀ (i : ι) (F : (ι → S) → ℝ), expect μ (condExp p i F) = expect μ F)
    (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hrow : ∀ i, ∑ k, C i k ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hsupp : ∀ i j, 1 < d i j → C i j = 0)
    (f g : (ι → S) → ℝ) :
    |covar μ f g|
      ≤ (∑ i, ∑ j, deltaAt i f * (α ^ (d i j) / (1 - α)) * deltaAt j g) / 4 := by
  have hC0 := majorant_nonneg hCdiag hC
  refine (covar_le_resolvent_tsum hμ0 hμ1 hp0 hp1 hloc hinv hCdiag hC
    hα0 hα1 hrow f g).trans ?_
  refine div_le_div_of_nonneg_right' ?_ (by norm_num)
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (deltaAt_nonneg j g)
  refine mul_le_mul_of_nonneg_left ?_ (deltaAt_nonneg i f)
  exact Matrix.tsum_pow_apply_le hC0 hα0 hα1 hrow hself htri hsupp i j

/-- The two-point form: for observables each depending on a single site, the
connected correlation decays exponentially in the distance between the two
sites, with rate `log(1/α)` and prefactor `1/(4(1-α))` — both read off the
single-site data, both free of the volume. -/
theorem covar_two_point {μ : (ι → S) → ℝ}
    {p : ι → (ι → S) → S → ℝ} {C : Matrix ι ι ℝ} {α : ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hloc : KernelLocal p)
    (hinv : ∀ (i : ι) (F : (ι → S) → ℝ), expect μ (condExp p i F) = expect μ F)
    (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hrow : ∀ i, ∑ k, C i k ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hsupp : ∀ i j, 1 < d i j → C i j = 0)
    (i₀ j₀ : ι) (f g : (ι → S) → ℝ)
    (hf : ∀ k, k ≠ i₀ → deltaAt k f = 0)
    (hg : ∀ k, k ≠ j₀ → deltaAt k g = 0) :
    |covar μ f g|
      ≤ deltaAt i₀ f * (α ^ (d i₀ j₀) / (1 - α)) * deltaAt j₀ g / 4 := by
  refine (covar_exp_decay hμ0 hμ1 hp0 hp1 hloc hinv hCdiag hC hα0 hα1 hrow
    d hself htri hsupp f g).trans ?_
  refine div_le_div_of_nonneg_right' ?_ (by norm_num)
  have houter : ∑ i, ∑ j, deltaAt i f * (α ^ (d i j) / (1 - α)) * deltaAt j g
      = ∑ j, deltaAt i₀ f * (α ^ (d i₀ j) / (1 - α)) * deltaAt j g := by
    refine Finset.sum_eq_single i₀ ?_ ?_
    · intro b _ hb
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hf b hb, zero_mul, zero_mul]
    · intro habs
      exact absurd (Finset.mem_univ i₀) habs
  have hinner : ∑ j, deltaAt i₀ f * (α ^ (d i₀ j) / (1 - α)) * deltaAt j g
      = deltaAt i₀ f * (α ^ (d i₀ j₀) / (1 - α)) * deltaAt j₀ g := by
    refine Finset.sum_eq_single j₀ ?_ ?_
    · intro b _ hb
      rw [hg b hb, mul_zero]
    · intro habs
      exact absurd (Finset.mem_univ j₀) habs
  rw [houter, hinner]

/-! ## §12  Non-vacuity, and the constant is the constant

One site, two states, the fair kernel, the uniform weight, `C = 0`, `α = 0`,
`d = 0`.  Every hypothesis of `covar_two_point` is discharged by computation —
so the hypotheses are jointly satisfiable — and on the indicator observable the
conclusion is an EQUALITY: `|Cov| = 1/4` against a bound whose value is `1/4`.
This is the Bernoulli control of gate J10q, now inside the kernel. -/

namespace Witness

/-- The fair single-site kernel: one site, two states. -/
noncomputable def pW : Fin 1 → (Fin 1 → Fin 2) → Fin 2 → ℝ := fun _ _ _ => 1 / 2

/-- The uniform weight on the two configurations. -/
noncomputable def muW : (Fin 1 → Fin 2) → ℝ := fun _ => 1 / 2

/-- The indicator observable. -/
noncomputable def fW : (Fin 1 → Fin 2) → ℝ := fun η => if η 0 = 1 then 1 else 0

/-- The configuration space of one site is its state space. -/
def eW : (Fin 1 → Fin 2) ≃ Fin 2 := Equiv.funUnique (Fin 1) (Fin 2)

theorem sum_omega (F : (Fin 1 → Fin 2) → ℝ) :
    ∑ η, F η = ∑ s : Fin 2, F (fun _ => s) := by
  rw [← Equiv.sum_comp eW.symm F]
  exact Finset.sum_congr rfl fun s _ => rfl

theorem pW_nonneg : ∀ (i : Fin 1) (η : Fin 1 → Fin 2) (s : Fin 2),
    0 ≤ pW i η s := fun _ _ _ => by norm_num [pW]

theorem pW_sum : ∀ (i : Fin 1) (η : Fin 1 → Fin 2), ∑ s, pW i η s = 1 := by
  intro i η
  simp only [pW]
  rw [Fin.sum_univ_two]
  norm_num

theorem pW_local : KernelLocal pW := fun _ _ _ _ => rfl

theorem muW_nonneg : ∀ η, 0 ≤ muW η := fun _ => by norm_num [muW]

theorem muW_sum : ∑ η, muW η = 1 := by
  rw [sum_omega muW]
  simp only [muW]
  rw [Fin.sum_univ_two]
  norm_num

theorem condExp_pW (F : (Fin 1 → Fin 2) → ℝ) (η : Fin 1 → Fin 2) :
    condExp pW 0 F η = (F (fun _ => 0) + F (fun _ => 1)) / 2 := by
  have hupd : ∀ s : Fin 2, Function.update η 0 s = fun _ => s := by
    intro s
    funext j
    have hj : j = 0 := Subsingleton.elim j 0
    rw [hj, update_self']
  have h0 : condExp pW 0 F η = ∑ s, pW 0 η s * F (Function.update η 0 s) := rfl
  have hcong : (∑ s, pW 0 η s * F (Function.update η 0 s))
      = ∑ s, pW 0 η s * F (fun _ => s) :=
    Finset.sum_congr rfl fun s _ => by rw [hupd s]
  rw [h0, hcong]
  simp only [pW]
  rw [Fin.sum_univ_two]
  ring

theorem pW_inv : ∀ (i : Fin 1) (F : (Fin 1 → Fin 2) → ℝ),
    expect muW (condExp pW i F) = expect muW F := by
  intro i F
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  have hLHS : expect muW (condExp pW 0 F)
      = (F (fun _ => 0) + F (fun _ => 1)) / 2 := by
    unfold expect
    have hcong : (∑ η, muW η * condExp pW 0 F η)
        = ∑ η, muW η * ((F (fun _ => 0) + F (fun _ => 1)) / 2) :=
      Finset.sum_congr rfl fun η _ => by rw [condExp_pW F η]
    rw [hcong, ← Finset.sum_mul, muW_sum, one_mul]
  have hRHS : expect muW F = (F (fun _ => 0) + F (fun _ => 1)) / 2 := by
    unfold expect
    rw [sum_omega (fun η => muW η * F η)]
    simp only [muW]
    rw [Fin.sum_univ_two]
    ring
  rw [hLHS, hRHS]

theorem covar_W : covar muW fW fW = 1 / 4 := by
  unfold covar expect
  rw [sum_omega (fun η => muW η * (fW η * fW η)),
    sum_omega (fun η => muW η * fW η)]
  simp only [muW, fW]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num

theorem deltaAt_fW : deltaAt 0 fW = 1 := by
  refine le_antisymm (deltaAt_le 0 fW fun η s => ?_) ?_
  · unfold fW
    rw [update_self' η 0 s]
    have h1 : (0 : ℝ) ≤ if η 0 = 1 then (1 : ℝ) else 0 := by
      split <;> norm_num
    have h2 : (if η 0 = 1 then (1 : ℝ) else 0) ≤ 1 := by
      split <;> norm_num
    have h3 : (0 : ℝ) ≤ if s = 1 then (1 : ℝ) else 0 := by
      split <;> norm_num
    have h4 : (if s = 1 then (1 : ℝ) else 0) ≤ 1 := by
      split <;> norm_num
    rw [abs_le]
    constructor <;> linarith
  · have hne01 : (0 : Fin 2) ≠ 1 := by decide
    have hv0 : fW (fun _ => 0) = 0 := by
      show (if (0 : Fin 2) = 1 then (1 : ℝ) else 0) = 0
      rw [if_neg hne01]
    have hv1 : fW (Function.update (fun _ => (0 : Fin 2)) 0 1) = 1 := by
      have hupd : Function.update (fun _ : Fin 1 => (0 : Fin 2)) 0 1 0 = 1 :=
        update_self' _ 0 1
      show (if Function.update (fun _ : Fin 1 => (0 : Fin 2)) 0 1 0 = 1
          then (1 : ℝ) else 0) = 1
      rw [hupd, if_pos rfl]
    have h := abs_sub_update_le_deltaAt 0 fW (fun _ => (0 : Fin 2)) 1
    rw [hv0, hv1] at h
    have habs : |(0 : ℝ) - 1| = 1 := by
      rw [zero_sub, abs_neg, abs_one]
    rw [habs] at h
    exact h

/-- **Non-vacuity.**  The comparison estimate applies to the witness data; its
hypotheses are jointly satisfiable. -/
theorem witness_bound :
    |covar muW fW fW|
      ≤ deltaAt 0 fW * ((0 : ℝ) ^ (0 : ℕ) / (1 - 0)) * deltaAt 0 fW / 4 :=
  covar_two_point (μ := muW) (p := pW)
    (C := (0 : Matrix (Fin 1) (Fin 1) ℝ)) (α := (0 : ℝ))
    muW_nonneg muW_sum pW_nonneg pW_sum pW_local pW_inv
    (fun _ => rfl)
    (fun i k _ η η' _ => le_of_eq (TV_self (pW i η)))
    (le_refl 0) (by norm_num)
    (fun _ => le_of_eq (Finset.sum_eq_zero fun _ _ => rfl))
    (fun _ _ => 0) (fun _ => rfl) (fun _ _ _ => Nat.zero_le _)
    (fun _ _ hij => absurd hij (Nat.not_lt_zero 1))
    0 0 fW fW
    (fun k hk => absurd (Subsingleton.elim k 0) hk)
    (fun k hk => absurd (Subsingleton.elim k 0) hk)

/-- **The constant is the constant.**  On the witness, the bound of
`covar_two_point` is an equality: `|Cov| = 1/4` against `1·(0⁰/(1-0))·1/4 =
1/4`.  The quarter of J10q cannot be lowered, now as a kernel-checked fact. -/
theorem witness_attained :
    |covar muW fW fW|
      = deltaAt 0 fW * ((0 : ℝ) ^ (0 : ℕ) / (1 - 0)) * deltaAt 0 fW / 4 := by
  rw [covar_W, deltaAt_fW, abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)]
  norm_num

end Witness

end Dobrushin

end YangMills.OS
