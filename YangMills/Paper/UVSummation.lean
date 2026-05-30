/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Honest formalization of the §6.3 UV-summation mechanism

Third batch from the Eriksson paper (§6.3, "Summation over Scales", Theorem 6.3 —
"the core new contribution").  Unlike the §4/§6.1/§7 pieces, this is not mere
bookkeeping: it is a genuine real-analysis inequality — that the ultraviolet
remainders `R_k`, which decay geometrically across RG scales, sum to a finite tail.

`uv_geometric_summation`: if the per-scale UV errors satisfy `|R_k| ≤ M · r^k` with
`0 ≤ r < 1` (geometric decay in the scale index — exactly the form produced by the
single-scale bound of Lemma 6.2 together with the scale structure `a_k = a*/L^{k*-k}`),
then the total is uniformly bounded:

  `|∑_{k<n} R_k| ≤ M · (1 − r)⁻¹`,

independently of the number of scales `n`.  This is proved outright (no hypotheses
beyond the stated per-scale bound).

## Faithfulness note

This captures the **summability / finite-tail mechanism** of Theorem 6.3.  The
paper additionally tracks the explicit decay rate `c₀ = κL` by carrying the leading
factor: instantiating `M := M₀ · exp(−c₀·t)` (with `t = R/a*`) turns the conclusion
into `|∑ R_k| ≤ M₀(1−r)⁻¹ · exp(−c₀·t)`, i.e. exponential clustering in the distance
— which is then fed to `mass_gap_bound` (§7).  The super-geometric refinement
(`L^{k*-k}` in the exponent, sharpening `r`) is a strengthening of this bound, not
needed for the assembly.

This lemma is unconditional real analysis; it does not depend on Balaban's inputs.
Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.Paper

open scoped BigOperators

/-- **UV summation over scales (§6.3, summation mechanism).**
Geometrically-decaying per-scale errors sum to a finite tail `M·(1−r)⁻¹`,
uniformly in the number of scales. -/
theorem uv_geometric_summation
    (R : ℕ → ℝ) (M r : ℝ) (n : ℕ)
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ k, |R k| ≤ M * r ^ k) :
    |∑ k ∈ Finset.range n, R k| ≤ M * (1 - r)⁻¹ := by
  -- Partial geometric sum bound, proved elementarily from `geom_sum_mul`
  -- (avoids `tsum`): `(∑_{k<n} r^k)·(1−r) = 1 − r^n ≤ 1`, and `1 − r > 0`.
  have h1r : 0 < 1 - r := by linarith
  have hpow : (0 : ℝ) ≤ r ^ n := pow_nonneg hr0 n
  have key : (∑ k ∈ Finset.range n, r ^ k) * (1 - r) = 1 - r ^ n := by
    linear_combination -geom_sum_mul r n
  have hle1 : (∑ k ∈ Finset.range n, r ^ k) * (1 - r) ≤ 1 := by rw [key]; linarith
  have hgeom : ∑ k ∈ Finset.range n, r ^ k ≤ (1 - r)⁻¹ := by
    calc ∑ k ∈ Finset.range n, r ^ k
        = (∑ k ∈ Finset.range n, r ^ k) * (1 - r) * (1 - r)⁻¹ :=
          (mul_inv_cancel_right₀ h1r.ne' _).symm
      _ ≤ 1 * (1 - r)⁻¹ := mul_le_mul_of_nonneg_right hle1 (le_of_lt (inv_pos.mpr h1r))
      _ = (1 - r)⁻¹ := one_mul _
  calc |∑ k ∈ Finset.range n, R k|
      ≤ ∑ k ∈ Finset.range n, |R k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, M * r ^ k := Finset.sum_le_sum (fun k _ => hbound k)
    _ = M * ∑ k ∈ Finset.range n, r ^ k := by rw [← Finset.mul_sum]
    _ ≤ M * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeom hM
