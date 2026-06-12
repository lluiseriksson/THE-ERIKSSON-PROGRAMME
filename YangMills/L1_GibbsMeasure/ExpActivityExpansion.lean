/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

end YangMills
