/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.MarginalCoupling
import YangMills.Paper.ClusteringToGap

/-!
# The marginal-coupling UV mass-gap conditional (gauge-RG, honest YM coupling)

`docs/BALABAN-SOURCE-BOUNDS.md`, `docs/UV-SINGLE-SCALE-PLAN.md`.  The banked
assembly `lattice_mass_gap_of_per_scale_uv` (`Paper/ClusteringToGap.lean`)
collapses a per-scale remainder family with a **geometric** scale-profile
`rᵏ` into the lattice mass gap.  But the 4D Yang–Mills coupling is **marginal /
asymptotically free** — its scale-profile `g_k^{κ₀}` does NOT decay
geometrically (see `RG/MarginalCoupling.lean`).  This file generalizes the
assembly to an arbitrary nonnegative summable profile and specializes it to
the marginal coupling:

* **`uv_summable_summation`** — finite partial sums of `|R k| ≤ amp·w_k` are
  `≤ amp·S` whenever `w ≥ 0` is summable with `∑' w ≤ S` (`Summable.sum_le_tsum`).
* **`lattice_mass_gap_of_per_scale_uv_summable`** — the geometric-profile
  assembly generalized to any nonnegative summable `w_k`: from
  `|R_{t,k}| ≤ (C₂·e^{−c₀t})·w_k` (+ IR bound + covariance scale-sum), the
  lattice mass gap with constant `C₁ + C₂·S`.
* **`lattice_mass_gap_of_cluster_and_marginal_coupling`** — the honest YM
  end-to-end UV conditional: the coupling flows by the marginal recursion
  `g_{k+1} = g_k(1 − β g_k)` (asymptotically free), the carried Bałaban YM
  activity bound is `|R_{t,k}| ≤ (C₂·e^{−c₀t})·g_k^{κ₀}` (`κ₀ > 1`), and the
  gap follows with the finite constant `C₁ + C₂·∑_k g_k^{κ₀}`.  No geometric-
  coupling assumption; `hRpoly` is the sole carried YM-analytic input.

**Honest scope.**  `hRpoly` (the YM single-scale activity bound, Bałaban CMP
116 Lemma 3 / Large Field II) is **carried**, never proved here — it is the
genuine months-scale gauge construction.  And Bałaban's series proves UV
*stability*, not a mass gap: the `R_{t,k}`-as-covariance-remainder reading and
the IR clustering input are this repository's framing, carried explicitly.
Clay distance ~0% (<0.1%), unchanged.

**Source.**  Bałaban CMP 109 (marginal coupling renormalization); the
summation/assembly is `Paper/ClusteringToGap.lean`; strategy/framing Lluis
Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

open YangMills

/-- General summable-profile partial-sum bound: if `|R k| ≤ amp·w_k` with
`w ≥ 0` summable and `∑' w ≤ S`, every finite partial sum is `≤ amp·S`. -/
theorem uv_summable_summation (R : ℕ → ℝ) {amp S : ℝ} (w : ℕ → ℝ)
    (hamp : 0 ≤ amp) (hw : ∀ k, 0 ≤ w k) (hsum : Summable w) (hS : ∑' k, w k ≤ S)
    (hR : ∀ k, |R k| ≤ amp * w k) (N : ℕ) :
    |∑ k ∈ Finset.range N, R k| ≤ amp * S := by
  calc |∑ k ∈ Finset.range N, R k|
      ≤ ∑ k ∈ Finset.range N, |R k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, amp * w k := Finset.sum_le_sum (fun k _ => hR k)
    _ = amp * ∑ k ∈ Finset.range N, w k := by rw [Finset.mul_sum]
    _ ≤ amp * ∑' k, w k :=
        mul_le_mul_of_nonneg_left (hsum.sum_le_tsum (Finset.range N) (fun k _ => hw k)) hamp
    _ ≤ amp * S := mul_le_mul_of_nonneg_left hS hamp

/-- **UV assembly for an arbitrary nonnegative summable scale-profile.**  The
generalization of `lattice_mass_gap_of_per_scale_uv` from a geometric profile
`rᵏ` to any nonnegative summable `w_k` with `∑' w ≤ S`: from the per-scale
remainder bound `|R_{t,k}| ≤ (C₂·e^{−c₀t})·w_k` (plus the theorem-fed IR bound
and the covariance scale-sum), the lattice mass gap follows with constant
`C₁ + C₂·S`. -/
theorem lattice_mass_gap_of_per_scale_uv_summable
    (covIR covUV : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ) (w : ℕ → ℝ)
    (C1 C2 ε c0 S : ℝ)
    (hε : 0 < ε) (hc0 : 0 < c0) (hC2 : 0 ≤ C2)
    (hw : ∀ k, 0 ≤ w k) (hsum : Summable w) (hS : ∑' k, w k ≤ S)
    (hIRbound : ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hcovUV : ∀ t : ℕ, covUV t = ∑ k ∈ Finset.range (nsc t), Rsc t k)
    (hRsc : ∀ t k : ℕ,
      |Rsc t k| ≤ (C2 * Real.exp (-(c0 * (t : ℝ)))) * w k) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV t| ≤ (C1 + C2 * S) * Real.exp (-(gap * (t : ℝ))) := by
  have hUV : ∀ t : ℕ,
      |covUV t| ≤ (C2 * S) * Real.exp (-(c0 * (t : ℝ))) := by
    intro t
    have hamp : (0 : ℝ) ≤ C2 * Real.exp (-(c0 * (t : ℝ))) :=
      mul_nonneg hC2 (Real.exp_pos _).le
    have hsumm := uv_summable_summation (Rsc t) w hamp hw hsum hS (fun k => hRsc t k) (nsc t)
    rw [hcovUV t]
    calc |∑ k ∈ Finset.range (nsc t), Rsc t k|
        ≤ (C2 * Real.exp (-(c0 * (t : ℝ)))) * S := hsumm
      _ = (C2 * S) * Real.exp (-(c0 * (t : ℝ))) := by ring
  exact lattice_mass_gap_of_exp_clustering_uniform covIR covUV C1 (C2 * S) ε c0
    hε hc0 hIRbound hUV

/-- **End-to-end UV conditional with the MARGINAL (Yang–Mills) coupling.**  The
honest 4D-YM replacement for `lattice_mass_gap_of_cluster_and_coupling`: the
coupling flows by the marginal recursion `g_{k+1} = g_k(1 − β g_k)`
(asymptotically free, NOT geometric), and the carried Bałaban YM activity
bound is `|R_{t,k}| ≤ (C₂·e^{−c₀t})·g_k^{κ₀}` with `κ₀ > 1`.  Although `g_k`
does not decay geometrically, `∑ g_k^{κ₀}` converges
(`marginal_coupling_pow_summable_of_recursion`), so the lattice mass gap
follows with the finite constant `C₁ + C₂·∑_k g_k^{κ₀}`.  No geometric-coupling
assumption; `hRpoly` is the sole carried YM-analytic input. -/
theorem lattice_mass_gap_of_cluster_and_marginal_coupling
    (covIR covUV : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ) (g : ℕ → ℝ)
    {C1 C2 ε c0 β κ₀ : ℝ}
    (hε : 0 < ε) (hc0 : 0 < c0) (hC2 : 0 ≤ C2) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k) (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hIRbound : ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hcovUV : ∀ t : ℕ, covUV t = ∑ k ∈ Finset.range (nsc t), Rsc t k)
    (hRpoly : ∀ t k : ℕ,
      |Rsc t k| ≤ (C2 * Real.exp (-(c0 * (t : ℝ)))) * g k ^ κ₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV t|
        ≤ (C1 + C2 * ∑' k, g k ^ κ₀) * Real.exp (-(gap * (t : ℝ))) := by
  have hsum : Summable (fun k => g k ^ κ₀) :=
    marginal_coupling_pow_summable_of_recursion g hβ hpos hsmall hrec hκ
  have hw : ∀ k, 0 ≤ g k ^ κ₀ := fun k => Real.rpow_nonneg (hpos k).le _
  exact lattice_mass_gap_of_per_scale_uv_summable covIR covUV Rsc nsc
    (fun k => g k ^ κ₀) C1 C2 ε c0 (∑' k, g k ^ κ₀)
    hε hc0 hC2 hw hsum le_rfl hIRbound hcovUV hRpoly

/-- **Non-vacuity of the marginal-coupling recursion.**  The logistic flow
`g_{k+1} = g_k(1 − β g_k)` with `β = 1`, `g_0 = 1/2` satisfies all the coupling
hypotheses of `lattice_mass_gap_of_cluster_and_marginal_coupling` — positivity,
smallness `β·g_k < 1`, and the recursion — so the marginal conditional is not
vacuously applicable: its coupling premise set is inhabited by genuine data.
(The flow stays in `(0, 1/2]`, by induction.) -/
theorem exists_marginal_coupling_flow :
    ∃ (g : ℕ → ℝ) (β : ℝ), 0 < β ∧ (∀ k, 0 < g k) ∧ (∀ k, β * g k < 1) ∧
      (∀ k, g (k + 1) = g k * (1 - β * g k)) := by
  set g : ℕ → ℝ := fun k => Nat.rec (1 / 2 : ℝ) (fun _ x => x * (1 - x)) k with hg
  have hrec : ∀ k, g (k + 1) = g k * (1 - g k) := fun k => rfl
  have hinv : ∀ k, 0 < g k ∧ g k ≤ 1 / 2 := by
    intro k
    induction k with
    | zero => exact ⟨by rw [hg]; norm_num, by rw [hg]; norm_num⟩
    | succ n ih =>
      obtain ⟨hp, hle⟩ := ih
      rw [hrec n]
      exact ⟨by nlinarith, by nlinarith [sq_nonneg (g n - 1 / 2)]⟩
  refine ⟨g, 1, one_pos, fun k => (hinv k).1, fun k => ?_, fun k => ?_⟩
  · rw [one_mul]; linarith [(hinv k).2]
  · rw [hrec k, one_mul]

end YangMills.RG
