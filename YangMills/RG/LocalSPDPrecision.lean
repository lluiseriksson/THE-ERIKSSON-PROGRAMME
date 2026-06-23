/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.KernelDecay

/-!
# Local SPD precision: resolvent-first abstract kernel layer

This module is the first source-independent block for the route

`local coercive precision -> resolvent decay -> localized covariance/root data`.

It does **not** identify the Yang--Mills Wilson Hessian, prove a physical
spectral gap, construct `P^{-1/2}`, or build CMP116 activities.  Instead it
records two reusable deterministic facts:

* finite-range Neumann data for a small kernel packages directly into the
  existing `KernelDecay.finiteRange_resolvent_isExpDecay` theorem;
* the inverse-square-root binomial coefficients
  `choose (2n) n / 4^n` are bounded by `1`, so their geometric tails are
  controlled by the same scalar tail as a Neumann series.

The intended later use is: prove that a normalized precision perturbation has
the finite-range/smallness data below, then consume `resolvent_expDecay` and
the binomial-tail lemmas to localize resolvents and finite truncations before
connecting them to physical covariance-root certificates.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

variable {V : Type*}

/-- The Neumann resolvent kernel associated with the composition powers already
defined in `KernelDecay`.  It is the formal kernel of `(1 - K)^{-1}` in the
small-kernel regime. -/
noncomputable def neumannResolventKernel (K : V → V → ℝ) :
    V → V → ℝ :=
  fun x y => ∑' n, Kpow K n x y

/-- Source-independent finite-range data sufficient for exponential decay of a
Neumann resolvent.

This is a data structure, not a proposition, because it carries the numerical
constants `M`, `R`, `kappa`, `sigma`, and `S` that downstream estimates must
reuse.  The field `small` is the analytic smallness condition
`M * exp(kappa * R) * S < 1` required by the existing Neumann-series theorem. -/
structure LocalFiniteRangeResolventData
    (dist : V → V → ℝ) (K : V → V → ℝ) where
  M : ℝ
  R : ℝ
  kappa : ℝ
  sigma : ℝ
  S : ℝ
  M_nonneg : 0 ≤ M
  S_nonneg : 0 ≤ S
  sigma_nonneg : 0 ≤ sigma
  sigma_le_kappa : sigma ≤ kappa
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  triangle : ∀ x y z, dist x y ≤ dist x z + dist z y
  finiteRange : ∀ x y, R < dist x y → K x y = 0
  bound : ∀ x y, |K x y| ≤ M
  summable : ∀ x, Summable (fun z => Real.exp (-sigma * dist x z))
  tsum_le : ∀ x, ∑' z, Real.exp (-sigma * dist x z) ≤ S
  small : M * Real.exp (kappa * R) * S < 1

/-- The explicit amplitude produced by the finite-range Neumann resolvent
bound. -/
noncomputable def LocalFiniteRangeResolventData.resolventAmplitude
    {dist : V → V → ℝ} {K : V → V → ℝ}
    (H : LocalFiniteRangeResolventData dist K) : ℝ :=
  H.M * Real.exp (H.kappa * H.R) *
    (1 - H.M * Real.exp (H.kappa * H.R) * H.S)⁻¹

/-- Finite-range local precision data imply exponential decay of the Neumann
resolvent kernel.

This is the resolvent-first bridge in its abstract form.  All physical
content remains in the fields of `LocalFiniteRangeResolventData`; the proof is
only the already verified finite-range resolvent theorem with named constants. -/
theorem LocalFiniteRangeResolventData.resolvent_expDecay
    {dist : V → V → ℝ} {K : V → V → ℝ}
    (H : LocalFiniteRangeResolventData dist K) :
    ExpDecay dist H.resolventAmplitude (H.kappa - H.sigma)
      (neumannResolventKernel K) := by
  dsimp [LocalFiniteRangeResolventData.resolventAmplitude,
    neumannResolventKernel]
  exact finiteRange_resolvent_isExpDecay
    H.M_nonneg H.S_nonneg H.sigma_nonneg H.sigma_le_kappa
    H.dist_nonneg H.triangle H.finiteRange H.bound H.summable H.tsum_le
    H.small

/-- A coefficient sequence suitable for inverse-square-root Neumann estimates:
every coefficient is nonnegative and bounded by `1`. -/
def InverseSqrtCoefficientMajorant (coeff : ℕ → ℝ) : Prop :=
  ∀ n, 0 ≤ coeff n ∧ coeff n ≤ 1

/-- Any inverse-square-root majorant coefficient sequence gives a summable
geometric series for `0 <= q < 1`. -/
theorem inverseSqrtCoefficientMajorant_summable
    {coeff : ℕ → ℝ} (hcoeff : InverseSqrtCoefficientMajorant coeff)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n => coeff n * q ^ n) := by
  refine Summable.of_nonneg_of_le ?hnonneg ?hle
    (summable_geometric_of_lt_one hq0 hq1)
  · intro n
    exact mul_nonneg (hcoeff n).1 (pow_nonneg hq0 n)
  · intro n
    simpa using
      mul_le_mul_of_nonneg_right (hcoeff n).2 (pow_nonneg hq0 n)

/-- Closed scalar bound for an inverse-square-root majorant series. -/
theorem inverseSqrtCoefficientMajorant_tsum_le
    {coeff : ℕ → ℝ} (hcoeff : InverseSqrtCoefficientMajorant coeff)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n, coeff n * q ^ n) ≤ (1 - q)⁻¹ := by
  have hdom :=
    inverseSqrtCoefficientMajorant_summable hcoeff hq0 hq1
  have hgeo := summable_geometric_of_lt_one hq0 hq1
  have hle : ∀ n, coeff n * q ^ n ≤ q ^ n := by
    intro n
    simpa using
      mul_le_mul_of_nonneg_right (hcoeff n).2 (pow_nonneg hq0 n)
  calc
    (∑' n, coeff n * q ^ n) ≤ ∑' n, q ^ n :=
      Summable.tsum_le_tsum hle hdom hgeo
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

/-- Shifted geometric tail for inverse-square-root majorant coefficients.  This
is the scalar truncation estimate used by finite-range approximants to
`P^{-1/2}` once the normalized perturbation has norm/range ratio `q`. -/
theorem inverseSqrtCoefficientMajorant_tail_le
    {coeff : ℕ → ℝ} (hcoeff : InverseSqrtCoefficientMajorant coeff)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑' n, coeff (n + N) * q ^ (n + N)) ≤
      q ^ N * (1 - q)⁻¹ := by
  have hgeo : Summable (fun n => q ^ N * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (q ^ N)
  have hle : ∀ n, coeff (n + N) * q ^ (n + N) ≤ q ^ N * q ^ n := by
    intro n
    have hpow : q ^ (n + N) = q ^ N * q ^ n := by
      rw [pow_add, mul_comm]
    calc
      coeff (n + N) * q ^ (n + N) ≤ 1 * q ^ (n + N) :=
        mul_le_mul_of_nonneg_right (hcoeff (n + N)).2
          (pow_nonneg hq0 (n + N))
      _ = q ^ N * q ^ n := by
        rw [hpow, one_mul]
  have hnonneg :
      ∀ n, 0 ≤ coeff (n + N) * q ^ (n + N) := by
    intro n
    exact mul_nonneg (hcoeff (n + N)).1
      (pow_nonneg hq0 (n + N))
  have hdom :
      Summable (fun n => coeff (n + N) * q ^ (n + N)) :=
    Summable.of_nonneg_of_le hnonneg hle hgeo
  calc
    (∑' n, coeff (n + N) * q ^ (n + N)) ≤
        ∑' n, q ^ N * q ^ n :=
      Summable.tsum_le_tsum hle hdom hgeo
    _ = q ^ N * ∑' n, q ^ n := tsum_mul_left
    _ = q ^ N * (1 - q)⁻¹ := by
      rw [tsum_geometric_of_lt_one hq0 hq1]

/-- The scalar coefficients of `(1 - z)^{-1/2}`:
`choose(2n,n) / 4^n`. -/
noncomputable def inverseSqrtBinomialCoeff (n : ℕ) : ℝ :=
  (((2 * n).choose n : ℕ) : ℝ) / (4 : ℝ) ^ n

/-- The inverse-square-root binomial coefficients are bounded by `1`.  This
keeps the first truncation estimates independent of the later Catalan/Prüfer
optimizations. -/
theorem inverseSqrtBinomialCoeff_majorant :
    InverseSqrtCoefficientMajorant inverseSqrtBinomialCoeff := by
  intro n
  constructor
  · unfold inverseSqrtBinomialCoeff
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) n)
  · unfold inverseSqrtBinomialCoeff
    have hchooseNat : (2 * n).choose n ≤ 2 ^ (2 * n) :=
      Nat.choose_le_two_pow (2 * n) n
    have hchoose :
        (((2 * n).choose n : ℕ) : ℝ) ≤
          ((2 ^ (2 * n) : ℕ) : ℝ) := by
      exact_mod_cast hchooseNat
    have hden_pos : 0 < (4 : ℝ) ^ n :=
      pow_pos (by norm_num) n
    have hden : (4 : ℝ) ^ n = ((2 ^ (2 * n) : ℕ) : ℝ) := by
      norm_num [pow_mul]
    have hfrac :
        (((2 * n).choose n : ℕ) : ℝ) / (4 : ℝ) ^ n ≤
          ((2 ^ (2 * n) : ℕ) : ℝ) / (4 : ℝ) ^ n :=
      div_le_div_of_nonneg_right hchoose hden_pos.le
    have hone :
        ((2 ^ (2 * n) : ℕ) : ℝ) / (4 : ℝ) ^ n = 1 := by
      rw [hden]
      field_simp
    rw [hone] at hfrac
    exact hfrac

/-- Closed scalar bound for the inverse-square-root binomial series in the
geometric regime. -/
theorem inverseSqrtBinomialCoeff_tsum_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n, inverseSqrtBinomialCoeff n * q ^ n) ≤
      (1 - q)⁻¹ :=
  inverseSqrtCoefficientMajorant_tsum_le
    inverseSqrtBinomialCoeff_majorant hq0 hq1

/-- Shifted scalar tail for the inverse-square-root binomial series. -/
theorem inverseSqrtBinomialCoeff_tail_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑' n, inverseSqrtBinomialCoeff (n + N) * q ^ (n + N)) ≤
      q ^ N * (1 - q)⁻¹ :=
  inverseSqrtCoefficientMajorant_tail_le
    inverseSqrtBinomialCoeff_majorant hq0 hq1 N

end YangMills.RG
