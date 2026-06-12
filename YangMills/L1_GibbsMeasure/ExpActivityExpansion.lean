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

end YangMills
