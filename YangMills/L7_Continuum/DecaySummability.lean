import Mathlib
import YangMills.L7_Continuum.ContinuumLimit

namespace YangMills

/-!
## L7.2 — Multiscale Decay Summability and Quantitative Bound

Formalization of the multiscale polymer bound:
∑ exp(-κ · L^k) < ∞ for κ > 0, L > 1.

Also proves the explicit closed-form upper bound:
∑' k, exp(-κ · L^k) ≤ exp(-κ) / (1 - exp(-(κ·(L-1))))

This quantitative form is directly reusable in UV-suppression arguments
(Step 5 of UNCONDITIONALITY_ROADMAP.md): the RHS gives an explicit
rate controlling the polymer gas contribution at each renormalization scale.
-/

open Real Filter Topology

/-- Summability of the multiscale decay series `∑ exp(-κ · L^k)` for κ > 0, L > 1.
Proved via Bernoulli's inequality and geometric series comparison. -/
theorem multiscale_decay_summable {κ L : ℝ} (hκ : 0 < κ) (hL : 1 < L) :
    Summable (fun k : ℕ => exp (-κ * L ^ k)) := by
  have hd : 0 < L - 1 := sub_pos.mpr hL
  have hr0 : (0 : ℝ) < exp (-(κ * (L - 1))) := exp_pos _
  have hr1 : exp (-(κ * (L - 1))) < 1 :=
    exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hκ hd))
  have hdom : Summable (fun k : ℕ => exp (-κ) * exp (-(κ * (L - 1))) ^ k) :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_left _
  apply Summable.of_nonneg_of_le (fun k => exp_nonneg _) _ hdom
  intro k
  -- Identity: exp(-κ) * r^k = exp(-κ + k·log(r)), proved by induction
  have hid : exp (-κ) * exp (-(κ * (L - 1))) ^ k =
      exp (-κ + ↑k * (-(κ * (L - 1)))) := by
    induction k with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, ← exp_add]
      congr 1; push_cast; ring
  -- Bernoulli: L^k ≥ 1 + k·(L-1), so -κ·L^k ≤ -κ + k·(-(κ·(L-1)))
  have key : -κ * L ^ k ≤ -κ + ↑k * (-(κ * (L - 1))) := by
    rw [show -κ + ↑k * (-(κ * (L - 1))) = -κ * (1 + ↑k * (L - 1)) from by push_cast; ring]
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hκ.le)
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ L - 1 by linarith) k
    have heq : (1 : ℝ) + (L - 1) = L := by ring
    rw [heq] at h
    linarith
  exact (exp_le_exp.mpr key).trans_eq hid.symm

/-- **Quantitative bound**: the multiscale decay series is bounded above by the
closed-form expression `exp(-κ) / (1 - exp(-(κ·(L-1))))`.

This is the explicit UV-suppression rate used in Step 5: the bound shows
that polymer activities at scale `k` contribute at most `exp(-κ·L^k)`, and
the total activity across all scales is controlled by `exp(-κ) / (1 - r)`
where `r = exp(-(κ·(L-1))) < 1` is the geometric decay ratio.

Specifically, this bound controls the small-field polymer gas expansion
that appears in the Balaban renormalization group analysis. -/
theorem multiscale_decay_tsum_bound {κ L : ℝ} (hκ : 0 < κ) (hL : 1 < L) :
    ∑' k : ℕ, exp (-κ * L ^ k) ≤ exp (-κ) / (1 - exp (-(κ * (L - 1)))) := by
  have hd : 0 < L - 1 := sub_pos.mpr hL
  have hr0 : (0 : ℝ) < exp (-(κ * (L - 1))) := exp_pos _
  have hr1 : exp (-(κ * (L - 1))) < 1 :=
    exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hκ hd))
  have hdom : Summable (fun k : ℕ => exp (-κ) * exp (-(κ * (L - 1))) ^ k) :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_left _
  -- Pointwise bound (same as in multiscale_decay_summable)
  have hle : ∀ k : ℕ, exp (-κ * L ^ k) ≤ exp (-κ) * exp (-(κ * (L - 1))) ^ k := by
    intro k
    have hid : exp (-κ) * exp (-(κ * (L - 1))) ^ k =
        exp (-κ + ↑k * (-(κ * (L - 1)))) := by
      induction k with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ← mul_assoc, ih, ← exp_add]
        congr 1; push_cast; ring
    have key : -κ * L ^ k ≤ -κ + ↑k * (-(κ * (L - 1))) := by
      rw [show -κ + ↑k * (-(κ * (L - 1))) = -κ * (1 + ↑k * (L - 1)) from by push_cast; ring]
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hκ.le)
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ L - 1 by linarith) k
      have heq : (1 : ℝ) + (L - 1) = L := by ring
      rw [heq] at h
      linarith
    exact (exp_le_exp.mpr key).trans_eq hid.symm
  -- Bound the tsum by the geometric series tsum, then compute the latter
  calc ∑' k : ℕ, exp (-κ * L ^ k)
      ≤ ∑' k : ℕ, exp (-κ) * exp (-(κ * (L - 1))) ^ k :=
          (multiscale_decay_summable hκ hL).tsum_le_tsum hle hdom
    _ = exp (-κ) * ∑' k : ℕ, exp (-(κ * (L - 1))) ^ k := tsum_mul_left
    _ = exp (-κ) * (1 - exp (-(κ * (L - 1))))⁻¹ := by
          rw [tsum_geometric_of_lt_one hr0.le hr1]
    _ = exp (-κ) / (1 - exp (-(κ * (L - 1)))) := (div_eq_mul_inv _ _).symm

/-- **Abstract Kotecký-Preiss activity bound**: For c ≥ 0 and κ > log(1+c),
the polymer gas activity series ∑ c^n · exp(-κ·(n+1)) converges and is < 1.

This is the abstract KP convergence criterion with explicit threshold κ > log(1+c).
The bound shows the total polymer gas activity is controlled by exp(-κ)/(1 - c·exp(-κ)),
which is < 1 whenever κ exceeds the KP threshold log(1+c).

Directly applicable in the Balaban renormalization group analysis: with
activity weights z_n = c^n · exp(-κ·(n+1)) for n-polymer clusters,
this theorem guarantees the polymer gas partition function converges. -/
theorem abstract_kp_activity_bound (c κ : ℝ) (hc : 0 ≤ c)
    (hκ : log (1 + c) < κ) :
    ∑' n : ℕ, c ^ n * exp (-κ * (↑n + 1)) < 1 := by
  have h1c : 0 < 1 + c := by linarith
  have hexp_pos : 0 < exp (-κ) := exp_pos _
  have hr_bound : exp (-κ) < (1 + c)⁻¹ := by
    have h : (1 + c)⁻¹ = exp (-log (1 + c)) := by
      rw [exp_neg, exp_log h1c]
    rw [h]
    exact exp_lt_exp.mpr (by linarith)
  have hr_nn : 0 ≤ c * exp (-κ) := mul_nonneg hc hexp_pos.le
  have hr1 : c * exp (-κ) < 1 := by
    calc c * exp (-κ) ≤ c * (1 + c)⁻¹ :=
              mul_le_mul_of_nonneg_left hr_bound.le hc
         _ = c / (1 + c) := (div_eq_mul_inv c _).symm
         _ < 1 := by rw [div_lt_one h1c]; linarith
  have hkey : ∀ n : ℕ, c ^ n * exp (-κ * (↑n + 1)) =
              exp (-κ) * (c * exp (-κ)) ^ n := by
    intro n
    have hpow : exp (-κ) ^ n = exp (↑n * (-κ)) := by
      induction n with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, ih, ← exp_add]
        congr 1; push_cast; ring
    rw [mul_pow, hpow,
        show -κ * (↑n + 1) = ↑n * (-κ) + (-κ) from by push_cast; ring,
        exp_add]
    ring
  have hval : ∑' n : ℕ, c ^ n * exp (-κ * (↑n + 1)) =
              exp (-κ) / (1 - c * exp (-κ)) := by
    simp_rw [hkey]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr_nn hr1, ← div_eq_mul_inv]
  rw [hval]
  have hpos : 0 < 1 - c * exp (-κ) := by linarith
  rw [div_lt_one hpos]
  have hineq : (1 + c) * exp (-κ) < 1 :=
    calc (1 + c) * exp (-κ) < (1 + c) * (1 + c)⁻¹ :=
              mul_lt_mul_of_pos_left hr_bound h1c
         _ = 1 := mul_inv_cancel₀ h1c.ne'
  linarith

theorem HasContinuumMassGap.limit_unique {m_lat : LatticeMassProfile}
    {m1 m2 : ℝ}
    (h1 : Tendsto (renormalizedMass m_lat) atTop (nhds m1))
    (h2 : Tendsto (renormalizedMass m_lat) atTop (nhds m2)) :
    m1 = m2 :=
  tendsto_nhds_unique h1 h2

theorem HasContinuumMassGap.smul {m_lat : LatticeMassProfile} {c : ℝ} (hc : 0 < c)
    (h : HasContinuumMassGap m_lat) : HasContinuumMassGap (fun N => c * m_lat N) := by
  obtain ⟨m_phys, hm_pos, htend⟩ := h
  refine ⟨c * m_phys, mul_pos hc hm_pos, ?_⟩
  have heq : renormalizedMass (fun N => c * m_lat N) = fun N => c * renormalizedMass m_lat N := by
    funext N
    simp [renormalizedMass, mul_div_assoc]
  rw [heq]
  exact htend.const_mul c

/-- **C72-H (v0.88.0): Lattice mass profile tends to zero under any continuum mass gap**.
    If a lattice mass profile `m_lat` has a continuum mass gap, then `m_lat N → 0`
    as `N → ∞`.

    Proof: `m_lat N = renormalizedMass m_lat N * latticeSpacing N`.
    As `N → ∞`, `renormalizedMass m_lat N → m_phys` (from `HasContinuumMassGap`)
    and `latticeSpacing N → 0`.  So the product tends to `m_phys * 0 = 0`.

    Physical meaning: any lattice mass profile compatible with a finite continuum
    mass gap must itself go to zero — it scales with the lattice spacing `a(N) → 0`.
    This characterizes the necessary UV behavior of the lattice mass.

    Mathematical content: Direct work on `HasContinuumMassGap` (strong Clay target).
    Oracle: `[propext, Classical.choice, Quot.sound]` — no `yangMills_continuum_mass_gap`. --/
theorem HasContinuumMassGap.lattice_mass_tendsto_zero {m_lat : LatticeMassProfile}
    (h : HasContinuumMassGap m_lat) :
    Tendsto m_lat atTop (𝓝 0) := by
  obtain ⟨m_phys, _, htend⟩ := h
  have heq : ∀ N : ℕ, m_lat N = renormalizedMass m_lat N * latticeSpacing N := fun N =>
    (div_mul_cancel₀ (m_lat N) (ne_of_gt (latticeSpacing_pos N))).symm
  have key : Tendsto (fun N : ℕ => renormalizedMass m_lat N * latticeSpacing N) atTop (𝓝 0) := by
    have hmul := htend.mul latticeSpacing_tendsto_zero
    simpa [mul_zero] using hmul
  exact key.congr (fun N => (heq N).symm)

end YangMills
