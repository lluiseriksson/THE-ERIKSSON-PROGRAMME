import Mathlib
import YangMills.L7_Continuum.ContinuumLimit

namespace YangMills

/-!
## L7.2 — Multiscale Decay Summability

Formalization of the multiscale polymer bound:
∑ exp(-κ · L^k) < ∞ for κ > 0, L > 1.

This supplies the geometric convergence sub-step
cited in UNCONDITIONALITY_ROADMAP.md §Step 5.
-/

open Real Filter Topology

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
  -- Identity: exp(-κ) * r^k = exp(-κ + k*log(r)), proved by induction
  have hid : exp (-κ) * exp (-(κ * (L - 1))) ^ k =
      exp (-κ + ↑k * (-(κ * (L - 1)))) := by
    induction k with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, ← exp_add]
      congr 1; push_cast; ring
  -- Bernoulli: L^k ≥ 1 + k*(L-1), so -κ*L^k ≤ -κ + k*(-(κ*(L-1)))
  have key : -κ * L ^ k ≤ -κ + ↑k * (-(κ * (L - 1))) := by
    rw [show -κ + ↑k * (-(κ * (L - 1))) = -κ * (1 + ↑k * (L - 1)) from by push_cast; ring]
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hκ.le)
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ L - 1 by linarith) k
    have heq : (1 : ℝ) + (L - 1) = L := by ring
    rw [heq] at h
    linarith
  exact (exp_le_exp.mpr key).trans_eq hid.symm

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

end YangMills
