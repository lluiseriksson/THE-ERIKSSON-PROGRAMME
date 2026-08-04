/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinComparison

/-!
# D-7 — comparison of two finite-volume Gibbs specifications

This is the new analytic brick needed to pass from within-volume Dobrushin
decay to a thermodynamic limit.  Two probability weights live on the same
finite product space.  The first specification has influence majorant `C`;
the two single-site kernels differ by at most the explicit local defect `b`.
Random-scan telescoping gives the classical Dobrushin comparison estimate

```
|μ(f) - ν(f)|
  ≤ ∑ i, b i * ∑ j, (∑' n, (C^n) j i) * δ_j(f).
```

No Cauchy, convergence, infinite-volume state, or boundary-tail conclusion is
assumed.  The only cross-specification input is the pointwise total-variation
defect `TV (p i η) (q i η) ≤ b i`.  The transpose orientation is forced by
the convention that `C i k` measures the influence of a change at `k` on the
conditional at `i`.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-! ## Probability and one-site perturbation estimates -/

theorem TV_le_one_of_probability {u v : S → ℝ}
    (hu0 : ∀ s, 0 ≤ u s) (hu1 : ∑ s, u s = 1)
    (hv0 : ∀ s, 0 ≤ v s) (hv1 : ∑ s, v s = 1) :
    TV u v ≤ 1 := by
  unfold TV
  have hterm : ∀ s : S, |u s - v s| ≤ u s + v s := by
    intro s
    calc |u s - v s| ≤ |u s| + |v s| := abs_sub _ _
      _ = u s + v s := by rw [abs_of_nonneg (hu0 s), abs_of_nonneg (hv0 s)]
  have hsum : ∑ s, |u s - v s| ≤ 2 := by
    calc ∑ s, |u s - v s| ≤ ∑ s, (u s + v s) :=
          Finset.sum_le_sum fun s _ => hterm s
      _ = (∑ s, u s) + ∑ s, v s := Finset.sum_add_distrib
      _ = 2 := by rw [hu1, hv1]; norm_num
  linarith

/-- Two probability expectations differ by at most the oscillation. -/
theorem abs_expect_sub_expect_le_osc
    {μ ν : (ι → S) → ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hν0 : ∀ η, 0 ≤ ν η) (hν1 : ∑ η, ν η = 1)
    (f : (ι → S) → ℝ) :
    |expect μ f - expect ν f| ≤ osc f := by
  have hmass : ∑ η, μ η = ∑ η, ν η := hμ1.trans hν1.symm
  have htv := TV_le_one_of_probability hμ0 hμ1 hν0 hν1
  have hosc := osc_nonneg f
  calc |expect μ f - expect ν f|
      = |∑ η, (μ η - ν η) * f η| := by
          unfold expect
          rw [← Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_congr rfl fun η _ => by ring
    _ ≤ TV μ ν * osc f := abs_sum_sub_le_tv_mul_osc hmass f
    _ ≤ 1 * osc f := mul_le_mul_of_nonneg_right htv hosc
    _ = osc f := one_mul _

/-- A pointwise change of one single-site kernel costs its TV defect times the
oscillation of the observable at that site. -/
theorem abs_condExp_sub_condExp_le
    {p q : ι → (ι → S) → S → ℝ}
    (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hq1 : ∀ i η, ∑ s, q i η s = 1)
    {b : ι → ℝ}
    (hdefect : ∀ i η, TV (p i η) (q i η) ≤ b i)
    (i : ι) (f : (ι → S) → ℝ) (η : ι → S) :
    |condExp p i f η - condExp q i f η| ≤ b i * deltaAt i f := by
  have hmass : ∑ s, p i η s = ∑ s, q i η s :=
    (hp1 i η).trans (hq1 i η).symm
  have hosc : osc (fun s => f (Function.update η i s)) ≤ deltaAt i f :=
    osc_section_le_deltaAt i f η
  calc |condExp p i f η - condExp q i f η|
      = |∑ s, (p i η s - q i η s) * f (Function.update η i s)| := by
          unfold condExp
          rw [← Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ TV (p i η) (q i η) * osc (fun s => f (Function.update η i s)) :=
        abs_sum_sub_le_tv_mul_osc hmass _
    _ ≤ b i * deltaAt i f :=
        mul_le_mul (hdefect i η) hosc (osc_nonneg _)
          (le_trans (TV_nonneg _ _) (hdefect i η))

/-- One random-scan step for the two specifications differs by the averaged
single-site defect. -/
theorem abs_scan_sub_scan_le
    {p q : ι → (ι → S) → S → ℝ}
    (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hq1 : ∀ i η, ∑ s, q i η s = 1)
    {b : ι → ℝ}
    (hdefect : ∀ i η, TV (p i η) (q i η) ≤ b i)
    (f : (ι → S) → ℝ) (η : ι → S) :
    |scan p f η - scan q f η|
      ≤ (∑ i, b i * deltaAt i f) / (Fintype.card ι : ℝ) := by
  unfold scan
  rw [← sub_div, abs_div, abs_of_pos (card_pos_real (ι := ι))]
  refine div_le_div_of_nonneg_right' ?_ (card_pos_real (ι := ι))
  calc |(∑ i, condExp p i f η) - ∑ i, condExp q i f η|
      = |∑ i, (condExp p i f η - condExp q i f η)| := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |condExp p i f η - condExp q i f η| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, b i * deltaAt i f :=
        Finset.sum_le_sum fun i _ => abs_condExp_sub_condExp_le hp1 hq1 hdefect i f η

/-- Expectation form of the one-scan defect. -/
theorem abs_expect_scan_sub_scan_le
    {ν : (ι → S) → ℝ} (hν0 : ∀ η, 0 ≤ ν η) (hν1 : ∑ η, ν η = 1)
    {p q : ι → (ι → S) → S → ℝ}
    (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hq1 : ∀ i η, ∑ s, q i η s = 1)
    {b : ι → ℝ}
    (hdefect : ∀ i η, TV (p i η) (q i η) ≤ b i)
    (f : (ι → S) → ℝ) :
    |expect ν (scan p f) - expect ν (scan q f)|
      ≤ (∑ i, b i * deltaAt i f) / (Fintype.card ι : ℝ) := by
  have hlin : expect ν (scan p f) - expect ν (scan q f)
      = expect ν (fun η => scan p f η - scan q f η) := by
    unfold expect
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun η _ => by ring
  rw [hlin]
  exact abs_expect_le hν0 hν1 (abs_scan_sub_scan_le hp1 hq1 hdefect f)

/-! ## Finite telescoping and the resolvent limit -/

theorem expect_scanIter_sub_expect_telescope
    {ν : (ι → S) → ℝ} {p q : ι → (ι → S) → S → ℝ}
    (hinvq : ∀ (i : ι) (F : (ι → S) → ℝ),
      expect ν (condExp q i F) = expect ν F)
    (f : (ι → S) → ℝ) :
    ∀ N : ℕ,
      expect ν (scanIter p f N) - expect ν f
        = ∑ n ∈ Finset.range N,
            (expect ν (scan p (scanIter p f n))
              - expect ν (scan q (scanIter p f n))) := by
  intro N
  induction N with
  | zero => simp only [scanIter, sub_self, Finset.range_zero, Finset.sum_empty]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hq := expect_scan hinvq (scanIter p f N)
      simp only [scanIter]
      rw [hq]
      ring

/-- Finite comparison estimate.  The decaying remainder is kept visible; the
next theorem is the single place where it is sent to zero. -/
theorem measure_comparison_partial
    {μ ν : (ι → S) → ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hν0 : ∀ η, 0 ≤ ν η) (hν1 : ∑ η, ν η = 1)
    {p q : ι → (ι → S) → S → ℝ}
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hq1 : ∀ i η, ∑ s, q i η s = 1)
    (hloc : KernelLocal p)
    (hinvp : ∀ (i : ι) (F : (ι → S) → ℝ),
      expect μ (condExp p i F) = expect μ F)
    (hinvq : ∀ (i : ι) (F : (ι → S) → ℝ),
      expect ν (condExp q i F) = expect ν F)
    {C : Matrix ι ι ℝ} (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k)
    {α : ℝ} (hα0 : 0 ≤ α) (hrow : ∀ i, ∑ k, C i k ≤ α)
    {b : ι → ℝ} (hb0 : ∀ i, 0 ≤ b i)
    (hdefect : ∀ i η, TV (p i η) (q i η) ≤ b i)
    (f : (ι → S) → ℝ) (N : ℕ) :
    |expect μ f - expect ν f|
      ≤ ∑ i, b i * seriesPartial C (fun j => deltaAt j f) N i
        + (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N * ∑ j, deltaAt j f := by
  have hC0 := majorant_nonneg hCdiag hC
  have hδ0 : ∀ i, 0 ≤ deltaAt i f := fun i => deltaAt_nonneg i f
  have hμiter := expect_scanIter hinvp f N
  have htel := expect_scanIter_sub_expect_telescope (p := p) hinvq f N
  have hidentity : expect μ f - expect ν f
      = (expect μ (scanIter p f N) - expect ν (scanIter p f N))
        + ∑ n ∈ Finset.range N,
            (expect ν (scan p (scanIter p f n))
              - expect ν (scan q (scanIter p f n))) := by
    rw [hμiter, ← htel]
    ring
  have hrem : |expect μ (scanIter p f N) - expect ν (scanIter p f N)|
      ≤ (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N * ∑ j, deltaAt j f := by
    calc |expect μ (scanIter p f N) - expect ν (scanIter p f N)|
        ≤ osc (scanIter p f N) :=
          abs_expect_sub_expect_le_osc hμ0 hμ1 hν0 hν1 _
      _ ≤ ∑ j, deltaAt j (scanIter p f N) := osc_le_sum_deltaAt _
      _ ≤ ∑ j, scanStepIter C (fun k => deltaAt k f) N j :=
          Finset.sum_le_sum fun j _ =>
            deltaAt_scanIter_le hp0 hp1 hloc hCdiag hC f N j
      _ ≤ (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N * ∑ j, deltaAt j f :=
          sum_scanStepIter_le hC0 hα0 hrow hδ0 N
  have hstep : ∀ n : ℕ,
      |expect ν (scan p (scanIter p f n))
          - expect ν (scan q (scanIter p f n))|
        ≤ (∑ i, b i * scanStepIter C (fun j => deltaAt j f) n i)
            / (Fintype.card ι : ℝ) := by
    intro n
    refine (abs_expect_scan_sub_scan_le hν0 hν1 hp1 hq1 hdefect _).trans ?_
    refine div_le_div_of_nonneg_right' ?_ (card_pos_real (ι := ι))
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left
        (deltaAt_scanIter_le hp0 hp1 hloc hCdiag hC f n i) (hb0 i)
  have hsum :
      ∑ n ∈ Finset.range N,
          |expect ν (scan p (scanIter p f n))
            - expect ν (scan q (scanIter p f n))|
        ≤ ∑ i, b i * seriesPartial C (fun j => deltaAt j f) N i := by
    calc
      ∑ n ∈ Finset.range N,
          |expect ν (scan p (scanIter p f n))
            - expect ν (scan q (scanIter p f n))|
          ≤ ∑ n ∈ Finset.range N,
              (∑ i, b i * scanStepIter C (fun j => deltaAt j f) n i)
                / (Fintype.card ι : ℝ) :=
            Finset.sum_le_sum fun n _ => hstep n
      _ = (∑ i, b i * transportSum C (fun j => deltaAt j f) N i)
            / (Fintype.card ι : ℝ) := by
          rw [← Finset.sum_div]
          congr 1
          unfold transportSum
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => by
            rw [Finset.mul_sum]
      _ ≤ (∑ i, b i * ((Fintype.card ι : ℝ)
              * seriesPartial C (fun j => deltaAt j f) N i))
            / (Fintype.card ι : ℝ) := by
          refine div_le_div_of_nonneg_right' ?_ (card_pos_real (ι := ι))
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (transportSum_le hC0 hδ0 N i) (hb0 i)
      _ = ∑ i, b i * seriesPartial C (fun j => deltaAt j f) N i := by
          have hm : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt (card_pos_real (ι := ι))
          rw [div_eq_iff hm]
          calc
            ∑ i, b i * ((Fintype.card ι : ℝ)
                * seriesPartial C (fun j => deltaAt j f) N i)
                = ∑ i, (b i * seriesPartial C (fun j => deltaAt j f) N i)
                    * (Fintype.card ι : ℝ) :=
                  Finset.sum_congr rfl fun i _ => by ring
            _ = (∑ i, b i * seriesPartial C (fun j => deltaAt j f) N i)
                  * (Fintype.card ι : ℝ) := by
                rw [Finset.sum_mul]
  rw [hidentity]
  calc
    |(expect μ (scanIter p f N) - expect ν (scanIter p f N))
        + ∑ n ∈ Finset.range N,
            (expect ν (scan p (scanIter p f n))
              - expect ν (scan q (scanIter p f n)))|
      ≤ |expect μ (scanIter p f N) - expect ν (scanIter p f N)|
          + |∑ n ∈ Finset.range N,
              (expect ν (scan p (scanIter p f n))
              - expect ν (scan q (scanIter p f n)))| := abs_add_le' _ _
    _ ≤ |expect μ (scanIter p f N) - expect ν (scanIter p f N)|
          + ∑ n ∈ Finset.range N,
              |expect ν (scan p (scanIter p f n))
                - expect ν (scan q (scanIter p f n))| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N * ∑ j, deltaAt j f
          + ∑ i, b i * seriesPartial C (fun j => deltaAt j f) N i :=
        add_le_add hrem hsum
    _ = ∑ i, b i * seriesPartial C (fun j => deltaAt j f) N i
          + (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N * ∑ j, deltaAt j f :=
        add_comm _ _

/-- **D-7 comparison theorem.**  The classical resolvent comparison estimate,
proved by site-wise random-scan telescoping. -/
theorem measure_comparison_resolvent
    {μ ν : (ι → S) → ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hν0 : ∀ η, 0 ≤ ν η) (hν1 : ∑ η, ν η = 1)
    {p q : ι → (ι → S) → S → ℝ}
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hq1 : ∀ i η, ∑ s, q i η s = 1)
    (hloc : KernelLocal p)
    (hinvp : ∀ (i : ι) (F : (ι → S) → ℝ),
      expect μ (condExp p i F) = expect μ F)
    (hinvq : ∀ (i : ι) (F : (ι → S) → ℝ),
      expect ν (condExp q i F) = expect ν F)
    {C : Matrix ι ι ℝ} (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, C i k ≤ α)
    {b : ι → ℝ} (hb0 : ∀ i, 0 ≤ b i)
    (hdefect : ∀ i η, TV (p i η) (q i η) ≤ b i)
    (f : (ι → S) → ℝ) :
    |expect μ f - expect ν f|
      ≤ ∑ i, b i * ∑ j, (∑' n : ℕ, (C ^ n) j i) * deltaAt j f := by
  have hC0 := majorant_nonneg hCdiag hC
  have hδ0 : ∀ i, 0 ≤ deltaAt i f := fun i => deltaAt_nonneg i f
  have hsummable : ∀ j i, Summable fun n : ℕ => (C ^ n) j i := fun j i =>
    Summable.of_nonneg_of_le (fun n => Matrix.pow_apply_nonneg hC0 n j i)
      (fun n => Matrix.pow_apply_le hC0 hα0 hrow n j i)
      (summable_geometric_of_lt_one hα0 hα1)
  set A := ∑ i, b i * ∑ j, (∑' n : ℕ, (C ^ n) j i) * deltaAt j f with hA
  have hpartial : ∀ N,
      ∑ i, b i * seriesPartial C (fun j => deltaAt j f) N i ≤ A := by
    intro N
    rw [hA]
    refine Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left ?_ (hb0 i)
    rw [seriesPartial_eq_pow_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun j _ =>
      ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hδ0 j)
    exact Summable.sum_le_tsum (Finset.range N)
      (fun n _ => Matrix.pow_apply_nonneg hC0 n j i) (hsummable j i)
  have hbound : ∀ N,
      |expect μ f - expect ν f|
        ≤ A + (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N
          * ∑ j, deltaAt j f := by
    intro N
    exact (measure_comparison_partial hμ0 hμ1 hν0 hν1 hp0 hp1 hq1 hloc
      hinvp hinvq hCdiag hC hα0 hrow hb0 hdefect f N).trans
        (add_le_add (hpartial N) le_rfl)
  have hγ0 := gamma_nonneg (ι := ι) hα0
  have hγ1 := gamma_lt_one (ι := ι) hα1
  have hlim : Tendsto
      (fun N : ℕ => A + (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N
        * ∑ j, deltaAt j f) atTop (𝓝 A) := by
    have hpow : Tendsto
        (fun N : ℕ => (1 - (1 - α) / (Fintype.card ι : ℝ)) ^ N)
        atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1
    simpa using (hpow.mul_const (∑ j, deltaAt j f)).const_add A
  rw [hA]
  exact ge_of_tendsto hlim (Eventually.of_forall hbound)

/-- Geometric form used for boundary perturbations. -/
theorem measure_comparison_exp_decay
    {μ ν : (ι → S) → ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hν0 : ∀ η, 0 ≤ ν η) (hν1 : ∑ η, ν η = 1)
    {p q : ι → (ι → S) → S → ℝ}
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hq1 : ∀ i η, ∑ s, q i η s = 1)
    (hloc : KernelLocal p)
    (hinvp : ∀ (i : ι) (F : (ι → S) → ℝ),
      expect μ (condExp p i F) = expect μ F)
    (hinvq : ∀ (i : ι) (F : (ι → S) → ℝ),
      expect ν (condExp q i F) = expect ν F)
    {C : Matrix ι ι ℝ} (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, C i k ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hsupp : ∀ i j, 1 < d i j → C i j = 0)
    {b : ι → ℝ} (hb0 : ∀ i, 0 ≤ b i)
    (hdefect : ∀ i η, TV (p i η) (q i η) ≤ b i)
    (f : (ι → S) → ℝ) :
    |expect μ f - expect ν f|
      ≤ ∑ i, b i * ∑ j, (α ^ d j i / (1 - α)) * deltaAt j f := by
  have hC0 := majorant_nonneg hCdiag hC
  refine (measure_comparison_resolvent hμ0 hμ1 hν0 hν1 hp0 hp1 hq1 hloc
    hinvp hinvq hCdiag hC hα0 hα1 hrow hb0 hdefect f).trans ?_
  refine Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left ?_ (hb0 i)
  refine Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right ?_ (deltaAt_nonneg j f)
  exact Matrix.tsum_pow_apply_le hC0 hα0 hα1 hrow hself htri hsupp j i

/-! ## Boundary-localised form

The entrywise exponential estimate above must not be summed with the crude
bound `card ι * α^R`: that would destroy uniformity in the second volume.
Instead we keep the matrix powers until after summing the defect sites.  All
powers below the support distance vanish, and the remaining complete row is
bounded by `α^n`.  Thus the whole (possibly very large) exterior costs one
geometric tail and no volume factor. -/

private theorem geom_partial_le_boundary {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (k : ℕ) :
    ∑ m ∈ Finset.range k, α ^ m ≤ (1 - α)⁻¹ := by
  have hsum : Summable (fun m : ℕ => α ^ m) :=
    summable_geometric_of_lt_one hα0 hα1
  calc
    ∑ m ∈ Finset.range k, α ^ m ≤ ∑' m : ℕ, α ^ m :=
      Summable.sum_le_tsum _ (fun _ _ => pow_nonneg hα0 _) hsum
    _ = (1 - α)⁻¹ := tsum_geometric_of_lt_one hα0 hα1

private theorem geom_tail_partial_le {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (R N : ℕ) :
    ∑ n ∈ Finset.range N, (if R ≤ n then α ^ n else 0)
      ≤ α ^ R / (1 - α) := by
  have hpos : (0 : ℝ) < 1 - α := by linarith
  by_cases hN : N ≤ R
  · have hzero :
        ∑ n ∈ Finset.range N, (if R ≤ n then α ^ n else 0) = 0 :=
      Finset.sum_eq_zero fun n hn => by
        rw [if_neg (Nat.not_le.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hn) hN))]
    rw [hzero]
    exact div_nonneg (pow_nonneg hα0 _) hpos.le
  · push_neg at hN
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le R) hN.le]
    have h1 :
        ∑ n ∈ Finset.Ico 0 R, (if R ≤ n then α ^ n else 0) = 0 :=
      Finset.sum_eq_zero fun n hn => by
        rw [if_neg (Nat.not_le.mpr (Finset.mem_Ico.mp hn).2)]
    have h2 :
        ∑ n ∈ Finset.Ico R N, (if R ≤ n then α ^ n else 0)
          = ∑ n ∈ Finset.Ico R N, α ^ n :=
      Finset.sum_congr rfl fun n hn => by
        rw [if_pos (Finset.mem_Ico.mp hn).1]
    rw [h1, h2, zero_add, Finset.sum_Ico_eq_sum_range]
    simp only [pow_add]
    rw [← Finset.mul_sum, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (geom_partial_le_boundary hα0 hα1 _) (pow_nonneg hα0 _)

/-- Summing the resolvent over every defect site outside distance `R` costs
exactly one geometric tail.  In particular, no cardinality of the ambient
finite product appears. -/
theorem weighted_resolvent_far_le
    {C : Matrix ι ι ℝ} {d : ι → ι → ℕ} {α : ℝ}
    (hC0 : ∀ i k, 0 ≤ C i k)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, C i k ≤ α)
    (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hsupp : ∀ i k, 1 < d i k → C i k = 0)
    {b : ι → ℝ} (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1)
    (R : ℕ) (j : ι)
    (hfar : ∀ i, b i ≠ 0 → R ≤ d j i) :
    ∑ i, b i * ∑' n : ℕ, (C ^ n) j i ≤ α ^ R / (1 - α) := by
  have hsummable : ∀ i, Summable fun n : ℕ => (C ^ n) j i := fun i =>
    Summable.of_nonneg_of_le (fun n => Matrix.pow_apply_nonneg hC0 n j i)
      (fun n => Matrix.pow_apply_le hC0 hα0 hrow n j i)
      (summable_geometric_of_lt_one hα0 hα1)
  have hweighted : ∀ i, Summable fun n : ℕ => b i * (C ^ n) j i := fun i =>
    (hsummable i).mul_left (b i)
  have hmul :
      ∑ i, b i * ∑' n : ℕ, (C ^ n) j i
        = ∑ i, ∑' n : ℕ, b i * (C ^ n) j i := by
    exact Finset.sum_congr rfl fun i _ => by rw [tsum_mul_left]
  rw [hmul, ← Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun i n => b i * (C ^ n) j i) (fun i _ => hweighted i)]
  refine Real.tsum_le_of_sum_range_le
    (fun n => Finset.sum_nonneg fun i _ =>
      mul_nonneg (hb0 i) (Matrix.pow_apply_nonneg hC0 n j i)) ?_
  intro N
  refine (Finset.sum_le_sum fun n _ => ?_).trans
    (geom_tail_partial_le hα0 hα1 R N)
  by_cases hn : R ≤ n
  · rw [if_pos hn]
    calc
      ∑ i, b i * (C ^ n) j i ≤ ∑ i, (C ^ n) j i :=
        Finset.sum_le_sum fun i _ => by
          simpa using mul_le_mul_of_nonneg_right (hb1 i)
            (Matrix.pow_apply_nonneg hC0 n j i)
      _ ≤ α ^ n := Matrix.pow_rowSum_le hC0 hα0 hrow n j
  · rw [if_neg hn]
    refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
    by_cases hbi : b i = 0
    · rw [hbi, zero_mul]
    · have hnlt : n < R := Nat.lt_of_not_ge hn
      have hnd : n < d j i := lt_of_lt_of_le hnlt (hfar i hbi)
      rw [Matrix.pow_apply_eq_zero_of_lt_dist hself htri hsupp n j i hnd,
        mul_zero]

/-- **D-7 boundary comparison.**  If every nonzero single-site defect is at
distance at least `R` from every active coordinate of `f`, the two Gibbs
expectations differ by one volume-free Dobrushin tail. -/
theorem measure_comparison_boundary_decay
    {μ ν : (ι → S) → ℝ}
    (hμ0 : ∀ η, 0 ≤ μ η) (hμ1 : ∑ η, μ η = 1)
    (hν0 : ∀ η, 0 ≤ ν η) (hν1 : ∑ η, ν η = 1)
    {p q : ι → (ι → S) → S → ℝ}
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hq1 : ∀ i η, ∑ s, q i η s = 1)
    (hloc : KernelLocal p)
    (hinvp : ∀ (i : ι) (F : (ι → S) → ℝ),
      expect μ (condExp p i F) = expect μ F)
    (hinvq : ∀ (i : ι) (F : (ι → S) → ℝ),
      expect ν (condExp q i F) = expect ν F)
    {C : Matrix ι ι ℝ} (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S,
      (∀ j, j ≠ k → η j = η' j) → TV (p i η) (p i η') ≤ C i k)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, C i k ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hsupp : ∀ i j, 1 < d i j → C i j = 0)
    {b : ι → ℝ} (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1)
    (hdefect : ∀ i η, TV (p i η) (q i η) ≤ b i)
    (f : (ι → S) → ℝ) (R : ℕ)
    (hfar : ∀ i j, b i ≠ 0 → deltaAt j f ≠ 0 → R ≤ d j i) :
    |expect μ f - expect ν f|
      ≤ (α ^ R / (1 - α)) * ∑ j, deltaAt j f := by
  have hC0 := majorant_nonneg hCdiag hC
  refine (measure_comparison_resolvent hμ0 hμ1 hν0 hν1 hp0 hp1 hq1 hloc
    hinvp hinvq hCdiag hC hα0 hα1 hrow hb0 hdefect f).trans ?_
  calc
    ∑ i, b i * ∑ j, (∑' n : ℕ, (C ^ n) j i) * deltaAt j f
        = ∑ i, ∑ j, b i * ((∑' n : ℕ, (C ^ n) j i) * deltaAt j f) := by
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ = ∑ j, ∑ i, b i * ((∑' n : ℕ, (C ^ n) j i) * deltaAt j f) :=
      Finset.sum_comm
    _ = ∑ j, deltaAt j f * ∑ i, b i * ∑' n : ℕ, (C ^ n) j i := by
      exact Finset.sum_congr rfl fun j _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ j, deltaAt j f * (α ^ R / (1 - α)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hδ : deltaAt j f = 0
      · rw [hδ, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left
          (weighted_resolvent_far_le hC0 hα0 hα1 hrow hself htri hsupp
            hb0 hb1 R j (fun i hbi => hfar i j hbi hδ))
          (deltaAt_nonneg j f)
    _ = (α ^ R / (1 - α)) * ∑ j, deltaAt j f := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring

end Dobrushin

end YangMills.OS
