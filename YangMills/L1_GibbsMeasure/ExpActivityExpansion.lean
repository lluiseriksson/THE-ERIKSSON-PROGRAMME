/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# The Pi-Cauchy product (exact-activity campaign, E1)

`docs/AREA-LAW-EXACT-PLAN.md` E1: expanding the Wilson Boltzmann
factor `∏_p exp(zₚ)` plaquette-by-plaquette needs the finite product
of exponential series as a single sum over multiplicity functions:

    ∏_{i : Fin n} ∑'_k a i k  =  ∑'_{m : Fin n → ℕ} ∏_i a i (m i).

Mathlib provides the two-factor Cauchy product
(`tsum_mul_tsum_of_summable_norm`); this file iterates it along
`Fin.consEquiv`, carrying norm-summability through the induction.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

set_option maxHeartbeats 1000000 in
/-- Norm-summability of the multiplicity-product family. -/
theorem summable_norm_pi_prod : ∀ {n : ℕ} (a : Fin n → ℕ → ℂ),
    (∀ i, Summable fun k => ‖a i k‖) →
    Summable fun m : Fin n → ℕ => ‖∏ i, a i (m i)‖ := by
  intro n
  induction n with
  | zero =>
      intro a _
      exact Summable.of_finite
  | succ n ih =>
      intro a ha
      have h0 := ha 0
      -- hide the product behind an opaque local to keep `whnf` away
      set G : (Fin n → ℕ) → ℂ := fun m => ∏ i, a i.succ (m i) with hG
      have htail : Summable fun m => ‖G m‖ :=
        ih (fun i => a i.succ) (fun i => ha i.succ)
      have hprodfam := Summable.mul_norm (f := fun k => a 0 k)
        (g := G) h0 htail
      have hcongr : ∀ z : ℕ × (Fin n → ℕ),
          ‖a 0 z.1 * G z.2‖
          = ‖∏ i : Fin (n + 1),
              a i (Fin.cons (α := fun _ => ℕ) z.1 z.2 i)‖ := by
        intro z
        simp only [hG]
        congr 1
        rw [Fin.prod_univ_succ]
        congr 1
      have h2 : Summable fun z : ℕ × (Fin n → ℕ) =>
          ‖∏ i : Fin (n + 1),
            a i (Fin.cons (α := fun _ => ℕ) z.1 z.2 i)‖ :=
        hprodfam.congr hcongr
      exact ((Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).summable_iff).mp
        (by
          refine h2.congr fun z => ?_
          rfl)

set_option maxHeartbeats 1000000 in
/-- **The Pi-Cauchy product** (`Fin`-indexed): a finite product of
absolutely convergent series is the sum over multiplicity functions
of the term products. -/
theorem tsum_pi_prod : ∀ {n : ℕ} (a : Fin n → ℕ → ℂ),
    (∀ i, Summable fun k => ‖a i k‖) →
    (∏ i, ∑' k, a i k) = ∑' m : Fin n → ℕ, ∏ i, a i (m i) := by
  intro n
  induction n with
  | zero =>
      intro a _
      have h1 : (∑' m : Fin 0 → ℕ, ∏ i, a i (m i)) = 1 := by
        rw [tsum_eq_single (fun i => i.elim0)
          (fun m' hm' => absurd (Subsingleton.elim m' _) hm')]
        simp
      rw [h1]
      simp
  | succ n ih =>
      intro a ha
      have h0 := ha 0
      set G : (Fin n → ℕ) → ℂ := fun m => ∏ i, a i.succ (m i) with hG
      have htail : Summable fun m => ‖G m‖ :=
        summable_norm_pi_prod (fun i => a i.succ) (fun i => ha i.succ)
      have hmul := tsum_mul_tsum_of_summable_norm
        (f := fun k => a 0 k) (g := G) h0 htail
      rw [Fin.prod_univ_succ]
      rw [ih (fun i => a i.succ) (fun i => ha i.succ)]
      rw [show (∑' m : Fin n → ℕ, ∏ i, a i.succ (m i))
          = ∑' m, G m from rfl]
      rw [hmul]
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).tsum_eq
        (fun m => ∏ i : Fin (n + 1), a i (m i))]
      refine tsum_congr fun z => ?_
      simp only [hG]
      rw [show (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)) z
          = Fin.cons (α := fun _ => ℕ) z.1 z.2 from rfl]
      rw [Fin.prod_univ_succ]
      congr 1

/-- **The Pi-Cauchy product over an arbitrary `Fintype`** — the form
the plaquette-indexed expansion consumes. -/
theorem tsum_pi_prod' {ι : Type*} [Fintype ι] (a : ι → ℕ → ℂ)
    (ha : ∀ i, Summable fun k => ‖a i k‖) :
    (∏ i, ∑' k, a i k) = ∑' m : ι → ℕ, ∏ i, a i (m i) := by
  classical
  set e := (Fintype.equivFin ι).symm with he
  have h1 : (∏ i : ι, ∑' k, a i k)
      = ∏ j : Fin (Fintype.card ι), ∑' k, a (e j) k :=
    (Fintype.prod_equiv e (fun j => ∑' k, a (e j) k)
      (fun i => ∑' k, a i k) fun j => rfl).symm
  have h2 := tsum_pi_prod (fun j => a (e j)) (fun j => ha (e j))
  rw [h1, h2]
  rw [← (Equiv.arrowCongr (Fintype.equivFin ι) (Equiv.refl ℕ)).symm.tsum_eq
    (fun m : ι → ℕ => ∏ i, a i (m i))]
  refine tsum_congr fun m' => ?_
  refine Fintype.prod_equiv e
    (fun j => a (e j) (m' j))
    (fun i => a i ((Equiv.arrowCongr (Fintype.equivFin ι)
      (Equiv.refl ℕ)).symm m' i)) fun j => ?_
  show a (e j) (m' j) = a (e j)
    ((Equiv.arrowCongr (Fintype.equivFin ι) (Equiv.refl ℕ)).symm m' (e j))
  rw [show ((Equiv.arrowCongr (Fintype.equivFin ι)
    (Equiv.refl ℕ)).symm m') (e j) = m' ((Fintype.equivFin ι) (e j))
    from rfl]
  rw [show (Fintype.equivFin ι) (e j) = j from
    (Fintype.equivFin ι).apply_symm_apply j]

/-- **∫↔∑' interchange under uniform summable domination** (E2): for
a countable family of measurable observables pointwise dominated by a
summable sequence, the integral of the sum is the sum of the
integrals — the analytic step that turns the expanded Boltzmann
factor into a sum of multiplicity terms under the Haar integral. -/
theorem integral_tsum_of_bounded {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    {κ : Type*} [Countable κ] (F : κ → α → ℂ) (c : κ → ℝ)
    (hFm : ∀ m, Measurable (F m)) (hFb : ∀ m a, ‖F m a‖ ≤ c m)
    (hc0 : ∀ m, 0 ≤ c m) (hc : Summable c) :
    ∫ a, ∑' m, F m a ∂μ = ∑' m, ∫ a, F m a ∂μ := by
  refine MeasureTheory.integral_tsum
    (fun m => (hFm m).aestronglyMeasurable) ?_
  have hb : ∀ m, (∫⁻ a, ‖F m a‖ₑ ∂μ) ≤ ENNReal.ofReal (c m) := by
    intro m
    calc ∫⁻ a, ‖F m a‖ₑ ∂μ
        ≤ ∫⁻ _a, ENNReal.ofReal (c m) ∂μ := by
          refine MeasureTheory.lintegral_mono fun a => ?_
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (hFb m a)
      _ = ENNReal.ofReal (c m) := by
          rw [MeasureTheory.lintegral_const]
          simp
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
  rw [← ENNReal.ofReal_tsum_of_nonneg hc0 hc]
  exact ENNReal.ofReal_ne_top

/-- Norm-summability of the exponential series' coefficients. -/
theorem summable_norm_pow_div_factorial (z : ℂ) :
    Summable fun k : ℕ => ‖z ^ k / (Nat.factorial k : ℂ)‖ := by
  refine Summable.congr (Real.summable_pow_div_factorial ‖z‖)
    fun k => ?_
  rw [norm_div, norm_pow, Complex.norm_natCast]

/-- **The exp-product expansion (E4b, stage 1):** a finite product of
exponentials is the sum over multiplicity functions of the
term-products — the pointwise expansion of the exact Wilson
Boltzmann factor. -/
theorem prod_exp_eq_tsum_prod_pow {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (∏ i, Complex.exp (z i))
      = ∑' m : ι → ℕ, ∏ i, (z i) ^ (m i) / (Nat.factorial (m i) : ℂ) := by
  rw [Finset.prod_congr rfl fun i _ => show Complex.exp (z i)
    = ∑' k : ℕ, (z i) ^ k / (Nat.factorial k : ℂ) from by
      rw [Complex.exp_eq_exp_ℂ]
      exact congrFun NormedSpace.exp_eq_tsum_div (z i)]
  exact tsum_pi_prod' (fun i k => (z i) ^ k / (Nat.factorial k : ℂ))
    (fun i => summable_norm_pow_div_factorial (z i))

/-- **The complex shifted exponential series:** `exp z − 1` is the
power series with the constant term removed — every term carries a
factor `z` (exponent `≥ 1`). -/
theorem tsum_pow_succ_div_factorial_succ (z : ℂ) :
    (∑' k : ℕ, (z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ))
      = Complex.exp z - 1 := by
  have hexp : Complex.exp z
      = ∑' k : ℕ, (z) ^ k / (Nat.factorial k : ℂ) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact congrFun NormedSpace.exp_eq_tsum_div z
  have hsum : Summable fun k : ℕ => (z) ^ k / (Nat.factorial k : ℂ) :=
    (summable_norm_pow_div_factorial z).of_norm
  have h := hsum.tsum_eq_zero_add
  rw [← hexp] at h
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  rw [h]; ring

/-- **The pinned exp-product expansion (V4-1, stage 1):** a finite
product of `exp z − 1` factors is the sum over multiplicity functions
of SHIFTED term-products — every exponent is `≥ 1`, so the occupied
index set is the full carrier `ι`. -/
theorem prod_exp_sub_one_eq_tsum_prod_pow_succ {ι : Type*} [Fintype ι]
    (z : ι → ℂ) :
    (∏ i, (Complex.exp (z i) - 1))
      = ∑' m : ι → ℕ,
          ∏ i, (z i) ^ (m i + 1) / (Nat.factorial (m i + 1) : ℂ) := by
  rw [Finset.prod_congr rfl fun i _ =>
    (tsum_pow_succ_div_factorial_succ (z i)).symm]
  exact tsum_pi_prod' (fun i k => (z i) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ))
    (fun i => (summable_norm_pow_div_factorial (z i)).comp_injective
      (add_left_injective 1))

set_option maxHeartbeats 1000000 in
/-- Summability of the multiplicity-indexed exponential weights — the
dominating family for the E2 interchange in the exact area law. -/
theorem summable_prod_pow_div_factorial {ι : Type*} [Fintype ι]
    (x : ℝ) (hx : 0 ≤ x) :
    Summable fun m : ι → ℕ => ∏ i, x ^ (m i) / (Nat.factorial (m i) : ℝ) := by
  classical
  have hFin := summable_norm_pi_prod
    (a := fun (_ : Fin (Fintype.card ι)) k =>
      ((x : ℂ)) ^ k / (Nat.factorial k : ℂ))
    (fun _ => summable_norm_pow_div_factorial _)
  have hι : Summable fun m : ι → ℕ =>
      ‖∏ i, ((x : ℂ)) ^ (m i) / (Nat.factorial (m i) : ℂ)‖ := by
    refine ((Equiv.arrowCongr (Fintype.equivFin ι)
      (Equiv.refl ℕ)).symm.summable_iff).mp ?_
    refine hFin.congr fun m' => ?_
    congr 1
    refine Fintype.prod_equiv (Fintype.equivFin ι).symm _ _ fun j => ?_
    show ((x : ℂ)) ^ (m' j) / (Nat.factorial (m' j) : ℂ)
      = ((x : ℂ)) ^ ((Equiv.arrowCongr (Fintype.equivFin ι)
            (Equiv.refl ℕ)).symm m' ((Fintype.equivFin ι).symm j))
        / (Nat.factorial ((Equiv.arrowCongr (Fintype.equivFin ι)
            (Equiv.refl ℕ)).symm m' ((Fintype.equivFin ι).symm j)) : ℂ)
    rw [show ((Equiv.arrowCongr (Fintype.equivFin ι)
        (Equiv.refl ℕ)).symm m') ((Fintype.equivFin ι).symm j)
      = m' ((Fintype.equivFin ι) ((Fintype.equivFin ι).symm j))
      from rfl]
    rw [(Fintype.equivFin ι).apply_symm_apply j]
  refine hι.congr fun m => ?_
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx, Complex.norm_natCast]

set_option maxHeartbeats 1000000 in
/-- **The real Pi-Cauchy product** for nonnegative families —
the form the tail estimate factorizes through. -/
theorem tsum_pi_prod_nonneg {ι : Type*} [Fintype ι] (a : ι → ℕ → ℝ)
    (h0 : ∀ i k, 0 ≤ a i k) (ha : ∀ i, Summable (a i)) :
    (∏ i, ∑' k, a i k) = ∑' m : ι → ℕ, ∏ i, a i (m i) := by
  have hC := tsum_pi_prod' (fun i k => ((a i k : ℝ) : ℂ))
    (fun i => (ha i).congr fun k =>
      (by rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (h0 i k)] :
          ‖((a i k : ℝ) : ℂ)‖ = a i k).symm)
  refine Complex.ofReal_injective ?_
  calc ((∏ i, ∑' k, a i k : ℝ) : ℂ)
      = ∏ i, ∑' k, ((a i k : ℝ) : ℂ) := by
        rw [Complex.ofReal_prod]
        exact Finset.prod_congr rfl fun i _ => Complex.ofReal_tsum _
    _ = ∑' m : ι → ℕ, ∏ i, ((a i (m i) : ℝ) : ℂ) := hC
    _ = ((∑' m : ι → ℕ, ∏ i, a i (m i) : ℝ) : ℂ) := by
        rw [Complex.ofReal_tsum]
        exact tsum_congr fun m => (Complex.ofReal_prod _ _).symm

/-- The exponential series sums to `exp`. -/
theorem tsum_pow_div_factorial (x : ℝ) :
    (∑' k : ℕ, x ^ k / (Nat.factorial k : ℝ)) = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ]
  exact (congrFun NormedSpace.exp_eq_tsum_div x).symm

/-- The `k ≥ 1` tail of the exponential series sums to `exp x − 1` —
the per-plaquette factor of an OCCUPIED plaquette in the exact tail
estimate. -/
theorem tsum_pow_div_factorial_succ (x : ℝ) :
    (∑' k : ℕ, x ^ (k + 1) / (Nat.factorial (k + 1) : ℝ))
      = Real.exp x - 1 := by
  have hsum : Summable fun k : ℕ => x ^ k / (Nat.factorial k : ℝ) :=
    Real.summable_pow_div_factorial x
  have h := hsum.tsum_eq_zero_add
  rw [tsum_pow_div_factorial] at h
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  linarith

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The per-`S` constrained factorized sum** (tail lemma, T1): the
exponential weights summed over multiplicity functions occupying
every plaquette of `S` factorize into `(e^x − 1)` per occupied
plaquette and `e^x` per free one. -/
theorem tsum_shifted_prod_pow_div_factorial {ι : Type*} [Fintype ι]
    (x : ℝ) (hx : 0 ≤ x) (S : Finset ι) :
    (∑' m : ι → ℕ, if ∀ p ∈ S, 1 ≤ m p
        then ∏ i, x ^ (m i) / (Nat.factorial (m i) : ℝ) else 0)
      = (Real.exp x - 1) ^ S.card
          * Real.exp x ^ (Fintype.card ι - S.card) := by
  classical
  set φ : (ι → ℕ) → (ι → ℕ) :=
    fun n i => if i ∈ S then n i + 1 else n i with hφ
  have hφinj : Function.Injective φ := by
    intro n n' h
    funext i
    have hi := congrFun h i
    simp only [hφ] at hi
    by_cases hiS : i ∈ S
    · rw [if_pos hiS, if_pos hiS] at hi
      omega
    · rwa [if_neg hiS, if_neg hiS] at hi
  have hsupp : Function.support (fun m : ι → ℕ =>
      if ∀ p ∈ S, 1 ≤ m p
        then ∏ i, x ^ (m i) / (Nat.factorial (m i) : ℝ) else 0)
      ⊆ Set.range φ := by
    intro m hm
    have hcond : ∀ p ∈ S, 1 ≤ m p := by
      by_contra hnot
      exact hm (if_neg hnot)
    refine ⟨fun i => if i ∈ S then m i - 1 else m i, ?_⟩
    funext i
    simp only [hφ]
    by_cases hiS : i ∈ S
    · rw [if_pos hiS, if_pos hiS]
      have := hcond i hiS
      omega
    · rw [if_neg hiS, if_neg hiS]
  have htrans := hφinj.tsum_eq hsupp
  rw [← htrans]
  have hterm : ∀ n : ι → ℕ,
      (if ∀ p ∈ S, 1 ≤ φ n p
        then ∏ i, x ^ (φ n i) / (Nat.factorial (φ n i) : ℝ) else 0)
      = ∏ i, (if i ∈ S
          then x ^ (n i + 1) / (Nat.factorial (n i + 1) : ℝ)
          else x ^ (n i) / (Nat.factorial (n i) : ℝ)) := by
    intro n
    rw [if_pos (fun p hp => by simp [hφ, hp])]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hiS : i ∈ S
    · simp only [hφ, if_pos hiS]
    · simp only [hφ, if_neg hiS]
  rw [tsum_congr hterm]
  rw [← tsum_pi_prod_nonneg
    (fun i k => if i ∈ S
      then x ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)
      else x ^ k / (Nat.factorial k : ℝ))
    (fun i k => by
      dsimp only
      by_cases hiS : i ∈ S
      · rw [if_pos hiS]; positivity
      · rw [if_neg hiS]; positivity)
    (fun i => by
      by_cases hiS : i ∈ S
      · simp only [if_pos hiS]
        exact (Real.summable_pow_div_factorial x).comp_injective
          Nat.succ_injective
      · simp only [if_neg hiS]
        exact Real.summable_pow_div_factorial x)]
  have hper : ∀ i : ι,
      (∑' k : ℕ, (if i ∈ S
        then x ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)
        else x ^ k / (Nat.factorial k : ℝ)))
      = (if i ∈ S then Real.exp x - 1 else Real.exp x) := by
    intro i
    by_cases hiS : i ∈ S
    · simp only [if_pos hiS]
      exact tsum_pow_div_factorial_succ x
    · simp only [if_neg hiS]
      exact tsum_pow_div_factorial x
  rw [Finset.prod_congr rfl fun i _ => hper i]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 1
  · congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  · congr 1
    rw [show Finset.univ.filter (fun i => i ∉ S) = Finset.univ \ S from
      (Finset.sdiff_eq_filter _ _).symm]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]

set_option maxHeartbeats 1000000 in
/-- **THE TAIL ESTIMATE** (T2+T3): the exponential weights summed over
multiplicity functions occupying at least `A` plaquettes decay like
`(e^x − 1)^A` — the quantitative engine of the exact area law. -/
theorem tsum_constrained_prod_pow_div_factorial_le {ι : Type*}
    [Fintype ι] (x : ℝ) (hx : 0 ≤ x) (A : ℕ) :
    (∑' m : ι → ℕ, if A ≤ (Finset.univ.filter (fun i => m i ≠ 0)).card
        then ∏ i, x ^ (m i) / (Nat.factorial (m i) : ℝ) else 0)
      ≤ 2 ^ (Fintype.card ι) *
          ((Real.exp x - 1) ^ A * Real.exp x ^ (Fintype.card ι)) := by
  classical
  set f : (ι → ℕ) → ℝ :=
    fun m => ∏ i, x ^ (m i) / (Nat.factorial (m i) : ℝ) with hf
  have hf0 : ∀ m, 0 ≤ f m := fun m =>
    Finset.prod_nonneg fun i _ => by positivity
  have hfs : Summable f := summable_prod_pow_div_factorial x hx
  set gS : Finset ι → (ι → ℕ) → ℝ :=
    fun S m => if ∀ p ∈ S, 1 ≤ m p then f m else 0 with hgS
  have hgS0 : ∀ S m, 0 ≤ gS S m := fun S m => by
    by_cases h : ∀ p ∈ S, 1 ≤ m p
    · simp only [hgS, if_pos h]; exact hf0 m
    · simp only [hgS, if_neg h]
      exact le_rfl
  have hgSle : ∀ S m, gS S m ≤ f m := fun S m => by
    by_cases h : ∀ p ∈ S, 1 ≤ m p
    · simp only [hgS, if_pos h]
      exact le_refl _
    · simp only [hgS, if_neg h]; exact hf0 m
  have hgSs : ∀ S, Summable (gS S) := fun S =>
    hfs.of_nonneg_of_le (hgS0 S) (hgSle S)
  -- T2: pointwise union bound over `A`-subsets
  have hpt : ∀ m : ι → ℕ,
      (if A ≤ (Finset.univ.filter (fun i => m i ≠ 0)).card
        then f m else 0)
      ≤ ∑ S ∈ Finset.univ.powersetCard A, gS S m := by
    intro m
    by_cases hc : A ≤ (Finset.univ.filter (fun i => m i ≠ 0)).card
    · rw [if_pos hc]
      obtain ⟨S₀, hS₀sub, hS₀card⟩ :=
        Finset.exists_subset_card_eq hc
      have hS₀mem : S₀ ∈ Finset.univ.powersetCard A := by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hS₀card⟩
      have hval : gS S₀ m = f m := by
        have hcond : ∀ p ∈ S₀, 1 ≤ m p := by
          intro p hp
          have hmem := hS₀sub hp
          rw [Finset.mem_filter] at hmem
          omega
        simp only [hgS, if_pos hcond]
      calc f m = gS S₀ m := hval.symm
        _ ≤ ∑ S ∈ Finset.univ.powersetCard A, gS S m :=
          Finset.single_le_sum (fun S _ => hgS0 S m) hS₀mem
    · rw [if_neg hc]
      exact Finset.sum_nonneg fun S _ => hgS0 S m
  -- T3: sum, swap, evaluate per `S`, count
  have hlhs_s : Summable fun m : ι → ℕ =>
      (if A ≤ (Finset.univ.filter (fun i => m i ≠ 0)).card
        then f m else 0) := by
    refine hfs.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    · by_cases hc : A ≤ (Finset.univ.filter (fun i => m i ≠ 0)).card
      · simp only [if_pos hc]; exact hf0 m
      · simp only [if_neg hc]
        exact le_rfl
    · by_cases hc : A ≤ (Finset.univ.filter (fun i => m i ≠ 0)).card
      · simp only [if_pos hc]
        exact le_rfl
      · simp only [if_neg hc]; exact hf0 m
  have hsum_s : Summable fun m : ι → ℕ =>
      ∑ S ∈ Finset.univ.powersetCard A, gS S m :=
    summable_sum fun S _ => hgSs S
  refine le_trans (hlhs_s.tsum_le_tsum hpt hsum_s) ?_
  rw [Summable.tsum_finsetSum fun S _ => hgSs S]
  have hper : ∀ S ∈ Finset.univ.powersetCard A,
      (∑' m, gS S m)
      = (Real.exp x - 1) ^ A
          * Real.exp x ^ (Fintype.card ι - A) := by
    intro S hS
    have hcard : S.card = A :=
      (Finset.mem_powersetCard.mp hS).2
    rw [hgS]
    rw [show (∑' m, if ∀ p ∈ S, 1 ≤ m p then f m else 0)
        = (Real.exp x - 1) ^ S.card
            * Real.exp x ^ (Fintype.card ι - S.card) from
      tsum_shifted_prod_pow_div_factorial x hx S]
    rw [hcard]
  rw [Finset.sum_congr rfl hper]
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    nsmul_eq_mul]
  have h1exp : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
  have hpow : Real.exp x ^ (Fintype.card ι - A)
      ≤ Real.exp x ^ (Fintype.card ι) :=
    pow_le_pow_right₀ h1exp (Nat.sub_le _ _)
  have hchoose : ((Fintype.card ι).choose A : ℝ)
      ≤ 2 ^ (Fintype.card ι) := by
    have h2 : (Fintype.card ι).choose A ≤ 2 ^ (Fintype.card ι) := by
      by_cases h : A ≤ Fintype.card ι
      · calc (Fintype.card ι).choose A
            ≤ ∑ k ∈ Finset.range (Fintype.card ι + 1),
                (Fintype.card ι).choose k :=
              Finset.single_le_sum (fun k _ => Nat.zero_le _)
                (Finset.mem_range.mpr (by omega))
          _ = 2 ^ (Fintype.card ι) := Nat.sum_range_choose _
      · push_neg at h
        rw [Nat.choose_eq_zero_of_lt h]
        positivity
    exact_mod_cast h2
  have hnn : (0 : ℝ) ≤ (Real.exp x - 1) ^ A := by
    have : (0 : ℝ) ≤ Real.exp x - 1 := by linarith
    positivity
  calc ((Fintype.card ι).choose A : ℝ) *
        ((Real.exp x - 1) ^ A * Real.exp x ^ (Fintype.card ι - A))
      ≤ 2 ^ (Fintype.card ι) *
        ((Real.exp x - 1) ^ A * Real.exp x ^ (Fintype.card ι)) := by
        refine mul_le_mul hchoose ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hpow hnn
    _ = _ := rfl

end YangMills
