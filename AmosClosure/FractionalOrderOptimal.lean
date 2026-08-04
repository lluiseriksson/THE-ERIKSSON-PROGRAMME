/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.FractionalOrder
import AmosClosure.BesselNegative

/-!
# Optimal real-order domain for the fractional Bessel barrier

For `-1 < μ < ν`, this file proves the complete classification

`besselRatioReal μ x - besselRatioReal ν x < (ν - μ) / x` for every `x > 0`

if and only if `0 ≤ μ + ν`.  It also proves the classical strict lower
inequality throughout `-1 < μ < ν`.

The proof is entirely Riccati/recurrence based.  In particular, the boundary
`μ+ν=0` is closed by uniqueness for a scalar linear ODE, and necessity for
`μ+ν<0` follows from eventual monotonic growth of `x²` times the barrier gap;
no Bessel `K` function or asymptotic expansion is imported.
-/

open Set Filter Topology

namespace AmosClosure

/-- Derivative of the sharp barrier gap throughout the natural strip. -/
lemma fractionalBarrierGap_hasDerivAt_gt_neg_one (μ ν : ℝ) (hμ : -1 < μ)
    (hμν : μ < ν) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fractionalBarrierGap μ ν)
      (riccatiQReal μ x (besselRatioReal μ x) -
        riccatiQReal ν x (besselRatioReal ν x) + (ν - μ) / x ^ 2) x := by
  have hν : -1 < ν := lt_trans hμ hμν
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hμ' := besselRatioReal_hasDerivAt_gt_neg_one μ hμ hx
  have hν' := besselRatioReal_hasDerivAt_gt_neg_one ν hν hx
  have hb : HasDerivAt (fun y : ℝ => (ν - μ) / y) (-(ν - μ) / x ^ 2) x := by
    convert (hasDerivAt_const x (ν - μ)).div (hasDerivAt_id x) hx0 using 1 <;>
      simp only [id_eq] <;> field_simp <;> ring
  have h := (hμ'.sub hν').sub hb
  convert h using 1
  ring

/-- Exact inhomogeneous linear ODE for the signed barrier gap. -/
lemma fractionalBarrierGap_hasDerivAt_ode (μ ν : ℝ) (hμ : -1 < μ)
    (hμν : μ < ν) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fractionalBarrierGap μ ν)
      (-(besselRatioReal μ x + besselRatioReal ν x + (μ + ν + 1) / x) *
          fractionalBarrierGap μ ν x -
        (ν - μ) * (μ + ν) / x ^ 2) x := by
  have h := fractionalBarrierGap_hasDerivAt_gt_neg_one μ ν hμ hμν hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  convert h using 1
  unfold fractionalBarrierGap riccatiQReal
  field_simp [hx0]
  ring

/-- At a contact, the gap derivative has the exact orientation factor
`μ+ν`. -/
lemma fractionalBarrierGap_hasDerivAt_of_touch_gt_neg_one (μ ν : ℝ)
    (hμ : -1 < μ) (hμν : μ < ν) {x : ℝ} (hx : 0 < x)
    (htouch : fractionalBarrierGap μ ν x = 0) :
    HasDerivAt (fractionalBarrierGap μ ν)
      (-((ν - μ) * (μ + ν)) / x ^ 2) x := by
  have h := fractionalBarrierGap_hasDerivAt_ode μ ν hμ hμν hx
  convert h using 1 <;> simp [htouch] <;> ring

lemma fractionalBarrierGap_hasDerivAt_boundary (μ ν : ℝ)
    (hμ : -1 < μ) (hμν : μ < ν) (hsum : μ + ν = 0)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fractionalBarrierGap μ ν)
      (-(besselRatioReal μ x + besselRatioReal ν x + 1 / x) *
        fractionalBarrierGap μ ν x) x := by
  have h := fractionalBarrierGap_hasDerivAt_ode μ ν hμ hμν hx
  convert h using 1 <;> simp [hsum]

/-- The recurrence alone supplies a sharp-at-zero elementary upper bound. -/
lemma besselRatioReal_lt_recurrence (ν : ℝ) (hν : -1 < ν) {x : ℝ}
    (hx : 0 < x) : besselRatioReal ν x < x / (2 * (ν + 1)) := by
  have hI0 := besselIReal_pos_gt_neg_one ν hν hx
  have hI1 := besselIReal_pos_gt_neg_one (ν + 1) (by linarith) hx
  have hI2 := besselIReal_pos_gt_neg_one (ν + 2) (by linarith) hx
  have hrec := besselIReal_recurrence_gt_neg_one ν hν hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hcoef : 0 < 2 * (ν + 1) := by linarith
  have hrec' : 2 * (ν + 1) * besselIReal (ν + 1) x =
      x * (besselIReal ν x - besselIReal (ν + 2) x) := by
    field_simp [hx0] at hrec
    nlinarith
  unfold besselRatioReal
  rw [div_lt_div_iff₀ hI0 hcoef]
  nlinarith

/-- Reciprocal form of the three-term recurrence. -/
lemma one_div_besselRatioReal (ν : ℝ) (hν : -1 < ν) {x : ℝ}
    (hx : 0 < x) :
    1 / besselRatioReal ν x =
      2 * (ν + 1) / x + besselRatioReal (ν + 1) x := by
  have hI0 := besselIReal_pos_gt_neg_one ν hν hx
  have hI1 := besselIReal_pos_gt_neg_one (ν + 1) (by linarith) hx
  have hrec := besselIReal_recurrence_gt_neg_one ν hν hx
  unfold besselRatioReal
  field_simp [ne_of_gt hx, ne_of_gt hI0, ne_of_gt hI1]
  field_simp [ne_of_gt hx] at hrec
  rw [show ν + 1 + 1 = ν + 2 by ring]
  linear_combination hrec

/-- A lower recurrence bound obtained by one more upper step. -/
lemma besselRatioReal_gt_recurrence (ν : ℝ) (hν : -1 < ν) {x : ℝ}
    (hx : 0 < x) :
    1 / (2 * (ν + 1) / x + x / (2 * (ν + 2))) <
      besselRatioReal ν x := by
  have hρ := besselRatioReal_pos_gt_neg_one hν hx
  have hnext := besselRatioReal_lt_recurrence (ν + 1) (by linarith) hx
  have hrecip := one_div_besselRatioReal ν hν hx
  have hν1 : 0 < ν + 1 := by linarith
  have hν2 : 0 < ν + 2 := by linarith
  have hD : 0 < 2 * (ν + 1) / x + x / (2 * (ν + 2)) := by positivity
  have hinv : 1 / besselRatioReal ν x <
      2 * (ν + 1) / x + x / (2 * (ν + 2)) := by
    rw [hrecip]
    have h := add_lt_add_left hnext (2 * (ν + 1) / x)
    simpa [show ν + 1 + 1 = ν + 2 by ring] using h
  have h := one_div_lt_one_div_of_lt (one_div_pos.mpr hρ) hinv
  simpa [one_div_div] using h

/-- A stronger large-argument lower bound used to prove necessity without
asymptotic expansions. -/
lemma besselRatioReal_gt_three_halves (ν : ℝ) (hν : -1 < ν) {x : ℝ}
    (hx : 0 < x) (hxlarge : 12 * (ν + 1) * (ν + 2) ≤ x ^ 2) :
    3 * (ν + 2) / (2 * x) < besselRatioReal ν x := by
  have hbase := besselRatioReal_gt_recurrence ν hν hx
  have hA : 0 < ν + 1 := by linarith
  have hB : 0 < ν + 2 := by linarith
  have hD : 0 < 2 * (ν + 1) / x + x / (2 * (ν + 2)) := by positivity
  have hDbound :
      2 * (ν + 1) / x + x / (2 * (ν + 2)) ≤ 2 * x / (3 * (ν + 2)) := by
    field_simp [ne_of_gt hx, ne_of_gt hB]
    nlinarith
  have htarget : 3 * (ν + 2) / (2 * x) ≤
      1 / (2 * (ν + 1) / x + x / (2 * (ν + 2))) := by
    have hinv := one_div_le_one_div_of_le hD hDbound
    convert hinv using 1 <;> field_simp [ne_of_gt hx, ne_of_gt hB] <;> ring
  exact lt_of_le_of_lt htarget hbase

/-- One explicit seed radius works for both strict comparisons. -/
noncomputable def fractionalSeed (μ ν : ℝ) : ℝ :=
  min (1 / 2 : ℝ) ((μ + 1) * (ν - μ))

lemma fractionalSeed_pos (μ ν : ℝ) (hμ : -1 < μ) (hμν : μ < ν) :
    0 < fractionalSeed μ ν := by
  unfold fractionalSeed
  rw [lt_min_iff]
  constructor <;> nlinarith

lemma fractionalSeed_sq_lt (μ ν : ℝ) (hμ : -1 < μ) (hμν : μ < ν) :
    (fractionalSeed μ ν) ^ 2 < 2 * (μ + 1) * (ν - μ) := by
  have hs0 := fractionalSeed_pos μ ν hμ hμν
  have hs1 : fractionalSeed μ ν ≤ (1 / 2 : ℝ) := by
    exact min_le_left _ _
  have hs2 : fractionalSeed μ ν ≤ (μ + 1) * (ν - μ) := by
    exact min_le_right _ _
  nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hs1)]

lemma fractionalBarrierGap_seed_gt_neg_one (μ ν : ℝ) (hμ : -1 < μ)
    (hμν : μ < ν) :
    fractionalBarrierGap μ ν (fractionalSeed μ ν) < 0 := by
  have hs0 := fractionalSeed_pos μ ν hμ hμν
  have hρμ := besselRatioReal_lt_recurrence μ hμ hs0
  have hρν := besselRatioReal_pos_gt_neg_one (lt_trans hμ hμν) hs0
  have hsq := fractionalSeed_sq_lt μ ν hμ hμν
  have hA : 0 < 2 * (μ + 1) := by linarith
  have hbar : fractionalSeed μ ν / (2 * (μ + 1)) <
      (ν - μ) / fractionalSeed μ ν := by
    rw [div_lt_div_iff₀ hA hs0]
    nlinarith
  unfold fractionalBarrierGap
  linarith

lemma fractionalBarrierGap_lt_of_le_seed (μ ν : ℝ) (hμ : -1 < μ)
    (hμν : μ < ν) {x : ℝ} (hx : 0 < x)
    (hxs : x ≤ fractionalSeed μ ν) :
    fractionalBarrierGap μ ν x < 0 := by
  have hρμ := besselRatioReal_lt_recurrence μ hμ hx
  have hρν := besselRatioReal_pos_gt_neg_one (lt_trans hμ hμν) hx
  have hs0 := fractionalSeed_pos μ ν hμ hμν
  have hsq_seed := fractionalSeed_sq_lt μ ν hμ hμν
  have hsq : x ^ 2 < 2 * (μ + 1) * (ν - μ) := by
    nlinarith
  have hA : 0 < 2 * (μ + 1) := by linarith
  have hbar : x / (2 * (μ + 1)) < (ν - μ) / x := by
    rw [div_lt_div_iff₀ hA hx]
    nlinarith
  unfold fractionalBarrierGap
  linarith

lemma besselRatioReal_orderGap_seed_gt_neg_one (μ ν : ℝ) (hμ : -1 < μ)
    (hμν : μ < ν) :
    0 < besselRatioReal μ (fractionalSeed μ ν) -
      besselRatioReal ν (fractionalSeed μ ν) := by
  have hs0 := fractionalSeed_pos μ ν hμ hμν
  have hlow := besselRatioReal_gt_recurrence μ hμ hs0
  have hupp := besselRatioReal_lt_recurrence ν (lt_trans hμ hμν) hs0
  have hsq := fractionalSeed_sq_lt μ ν hμ hμν
  have hμ1 : 0 < μ + 1 := by linarith
  have hμ2 : 0 < μ + 2 := by linarith
  have hD : 0 < 2 * (μ + 1) / fractionalSeed μ ν +
      fractionalSeed μ ν / (2 * (μ + 2)) := by positivity
  have hB : 0 < 2 * (ν + 1) := by linarith
  have hcompare : fractionalSeed μ ν / (2 * (ν + 1)) <
      1 / (2 * (μ + 1) / fractionalSeed μ ν +
        fractionalSeed μ ν / (2 * (μ + 2))) := by
    rw [div_lt_div_iff₀ hB hD]
    field_simp [ne_of_gt hs0]
    nlinarith
  linarith

/-- At equality of two ratios, their difference has strictly positive
derivative. -/
lemma besselRatioReal_orderGap_hasDerivAt_of_eq (μ ν : ℝ) (hμ : -1 < μ)
    (hμν : μ < ν) {x : ℝ} (hx : 0 < x)
    (heq : besselRatioReal μ x = besselRatioReal ν x) :
    HasDerivAt (fun y => besselRatioReal μ y - besselRatioReal ν y)
      (2 * (ν - μ) / x * besselRatioReal ν x) x := by
  have hμ' := besselRatioReal_hasDerivAt_gt_neg_one μ hμ hx
  have hν' := besselRatioReal_hasDerivAt_gt_neg_one ν (lt_trans hμ hμν) hx
  have h := hμ'.sub hν'
  convert h using 1
  unfold riccatiQReal
  rw [heq]
  field_simp [ne_of_gt hx]
  ring

/-- Strict decrease of the ratio in its order on the full strip `ν>-1`. -/
theorem besselRatioReal_strictAnti_order (μ ν : ℝ) (hμ : -1 < μ)
    (hμν : μ < ν) {x : ℝ} (hx : 0 < x) :
    besselRatioReal ν x < besselRatioReal μ x := by
  let H : ℝ → ℝ := fun y => besselRatioReal μ y - besselRatioReal ν y
  set s := fractionalSeed μ ν with hs_def
  have hs0 : 0 < s := by simpa [hs_def] using fractionalSeed_pos μ ν hμ hμν
  have hsseed : 0 < H s := by
    simpa [H, hs_def] using besselRatioReal_orderGap_seed_gt_neg_one μ ν hμ hμν
  by_contra hcon
  push_neg at hcon
  have hxsgt : s < x := by
    by_contra hxs
    push_neg at hxs
    have hρμ := besselRatioReal_gt_recurrence μ hμ hx
    have hρν := besselRatioReal_lt_recurrence ν (lt_trans hμ hμν) hx
    have hsq : x ^ 2 < 2 * (μ + 1) * (ν - μ) := by
      have hs1 : s ≤ (1 / 2 : ℝ) := by
        rw [hs_def]
        exact min_le_left _ _
      have hs2 : s ≤ (μ + 1) * (ν - μ) := by
        rw [hs_def]
        exact min_le_right _ _
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr (le_trans hxs hs1))]
    have hμ1 : 0 < μ + 1 := by linarith
    have hμ2 : 0 < μ + 2 := by linarith
    have hD : 0 < 2 * (μ + 1) / x + x / (2 * (μ + 2)) := by positivity
    have hB : 0 < 2 * (ν + 1) := by linarith
    have hcompare : x / (2 * (ν + 1)) <
        1 / (2 * (μ + 1) / x + x / (2 * (μ + 2))) := by
      rw [div_lt_div_iff₀ hB hD]
      field_simp [ne_of_gt hx]
      nlinarith
    linarith
  set S := {y : ℝ | y ∈ Icc s x ∧ H y ≤ 0} with hS_def
  have hSne : S.Nonempty := by
    refine ⟨x, ⟨le_of_lt hxsgt, le_rfl⟩, ?_⟩
    exact sub_nonpos.mpr hcon
  have hSbdd : BddBelow S := ⟨s, fun y hy => hy.1.1⟩
  have hcont : ContinuousOn H (Icc s x) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hs0 hy.1
    exact ((besselRatioReal_hasDerivAt_gt_neg_one μ hμ hy0).sub
      (besselRatioReal_hasDerivAt_gt_neg_one ν (lt_trans hμ hμν) hy0)).continuousAt.continuousWithinAt
  have hSclosed : IsClosed S := by
    have : S = Icc s x ∩ H ⁻¹' Iic 0 := by
      ext y
      simp [hS_def]
    rw [this]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  set c := sInf S with hc_def
  have hcmem : c ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hsc : s ≤ c := le_csInf hSne (fun y hy => hy.1.1)
  have hc0 : 0 < c := lt_of_lt_of_le hs0 hsc
  have hcne : c ≠ s := by
    intro h
    rw [h] at hcmem
    linarith [hsseed, hcmem.2]
  have hsc' : s < c := lt_of_le_of_ne hsc (Ne.symm hcne)
  have hleft : ∀ y, s < y → y < c → 0 < H y := by
    intro y hsy hyc
    by_contra hy
    push_neg at hy
    have hymem : y ∈ S := by
      refine ⟨⟨le_of_lt hsy, ?_⟩, hy⟩
      exact le_of_lt (lt_of_lt_of_le hyc hcmem.1.2)
    exact absurd (csInf_le hSbdd hymem) (not_le.mpr hyc)
  have htendsto : Tendsto H (𝓝[<] c) (𝓝 (H c)) := by
    exact (((besselRatioReal_hasDerivAt_gt_neg_one μ hμ hc0).sub
      (besselRatioReal_hasDerivAt_gt_neg_one ν (lt_trans hμ hμν) hc0)).continuousAt.continuousWithinAt)
  have hev_ge : ∀ᶠ y in 𝓝[<] c, 0 ≤ H y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hsc')] with y hyc hsy
    exact (hleft y hsy hyc).le
  have hgap_ge : 0 ≤ H c := by
    exact isClosed_Ici.mem_of_tendsto htendsto (by
      simpa only [mem_Ici] using hev_ge)
  have htouch : H c = 0 := le_antisymm hcmem.2 hgap_ge
  have heq : besselRatioReal μ c = besselRatioReal ν c := by
    dsimp [H] at htouch
    linarith
  have hderiv := besselRatioReal_orderGap_hasDerivAt_of_eq μ ν hμ hμν hc0 heq
  have hρν := besselRatioReal_pos_gt_neg_one (lt_trans hμ hμν) hc0
  have hνμ : 0 < ν - μ := sub_pos.mpr hμν
  have hdpos : 0 < 2 * (ν - μ) / c * besselRatioReal ν c :=
    mul_pos (div_pos (mul_pos (by norm_num) hνμ) hc0) hρν
  have hslope : Tendsto (slope H c) (𝓝[<] c)
      (𝓝 (2 * (ν - μ) / c * besselRatioReal ν c)) := by
    have hd : HasDerivAt H (2 * (ν - μ) / c * besselRatioReal ν c) c := by
      simpa [H] using hderiv
    have h := hasDerivAt_iff_tendsto_slope.mp hd
    exact h.mono_left (nhdsWithin_mono c (fun y hy => ne_of_lt hy))
  have hev_slope : ∀ᶠ y in 𝓝[<] c, 0 < slope H c y :=
    hslope.eventually (isOpen_Ioi.mem_nhds hdpos)
  have hev_lt : ∀ᶠ y in 𝓝[<] c, H y < H c := by
    filter_upwards [hev_slope, self_mem_nhdsWithin] with y hsl hyc
    have hyc' : y - c < 0 := sub_neg.mpr hyc
    rw [slope_def_field] at hsl
    rcases div_pos_iff.mp hsl with ⟨hnum, hden⟩ | ⟨hnum, hden⟩
    · linarith [hden, hyc']
    · linarith [hnum]
  have hev_left : ∀ᶠ y in 𝓝[<] c, 0 < H y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hsc')] with y hyc hsy
    exact hleft y hsy hyc
  have : ∃ y, H y < H c ∧ 0 < H y := (hev_lt.and hev_left).exists
  obtain ⟨y, hy1, hy2⟩ := this
  rw [htouch] at hy1
  linarith

/-- The sharp barrier comparison throughout the part of the natural strip
where the first-contact vector field points strictly inward. -/
theorem besselRatioReal_fractional_upper_gt_neg_one_of_pos_sum
    (μ ν : ℝ) (hμ : -1 < μ) (hμν : μ < ν) (hsum : 0 < μ + ν)
    {x : ℝ} (hx : 0 < x) :
    besselRatioReal μ x - besselRatioReal ν x < (ν - μ) / x := by
  set s := fractionalSeed μ ν with hs_def
  have hs0 : 0 < s := by
    simpa [hs_def] using fractionalSeed_pos μ ν hμ hμν
  have hsseed : fractionalBarrierGap μ ν s < 0 := by
    simpa [hs_def] using fractionalBarrierGap_seed_gt_neg_one μ ν hμ hμν
  by_contra hcon
  push_neg at hcon
  have hxsgt : s < x := by
    by_contra hxs
    push_neg at hxs
    have hseed := fractionalBarrierGap_lt_of_le_seed μ ν hμ hμν hx (by
      simpa [hs_def] using hxs)
    unfold fractionalBarrierGap at hseed
    linarith
  set S := {y : ℝ | y ∈ Icc s x ∧ 0 ≤ fractionalBarrierGap μ ν y}
    with hS_def
  have hSne : S.Nonempty := by
    refine ⟨x, ⟨le_of_lt hxsgt, le_rfl⟩, ?_⟩
    unfold fractionalBarrierGap
    linarith
  have hSbdd : BddBelow S := ⟨s, fun y hy => hy.1.1⟩
  have hcont : ContinuousOn (fractionalBarrierGap μ ν) (Icc s x) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hs0 hy.1
    exact (fractionalBarrierGap_hasDerivAt_gt_neg_one μ ν hμ hμν hy0).continuousAt.continuousWithinAt
  have hSclosed : IsClosed S := by
    have : S = Icc s x ∩ fractionalBarrierGap μ ν ⁻¹' Ici 0 := by
      ext y
      simp [hS_def]
    rw [this]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  set c := sInf S with hc_def
  have hcmem : c ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hsc : s ≤ c := le_csInf hSne (fun y hy => hy.1.1)
  have hc0 : 0 < c := lt_of_lt_of_le hs0 hsc
  have hcne : c ≠ s := by
    intro h
    rw [h] at hcmem
    linarith [hsseed, hcmem.2]
  have hsc' : s < c := lt_of_le_of_ne hsc (Ne.symm hcne)
  have hleft : ∀ y, s < y → y < c → fractionalBarrierGap μ ν y < 0 := by
    intro y hsy hyc
    by_contra hy
    push_neg at hy
    have hymem : y ∈ S := by
      refine ⟨⟨le_of_lt hsy, ?_⟩, hy⟩
      exact le_of_lt (lt_of_lt_of_le hyc hcmem.1.2)
    exact absurd (csInf_le hSbdd hymem) (not_le.mpr hyc)
  have htendsto : Tendsto (fractionalBarrierGap μ ν) (𝓝[<] c)
      (𝓝 (fractionalBarrierGap μ ν c)) :=
    ((fractionalBarrierGap_hasDerivAt_gt_neg_one μ ν hμ hμν hc0).continuousAt.continuousWithinAt)
  have hev_le : ∀ᶠ y in 𝓝[<] c, fractionalBarrierGap μ ν y ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hsc')] with y hyc hsy
    exact (hleft y hsy hyc).le
  have hgap_le : fractionalBarrierGap μ ν c ≤ 0 :=
    le_of_tendsto htendsto hev_le
  have htouch : fractionalBarrierGap μ ν c = 0 :=
    le_antisymm hgap_le hcmem.2
  have hderiv := fractionalBarrierGap_hasDerivAt_of_touch_gt_neg_one
    μ ν hμ hμν hc0 htouch
  have hδ : 0 < ν - μ := sub_pos.mpr hμν
  have hprod : 0 < (ν - μ) * (μ + ν) := mul_pos hδ hsum
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc0
  have hdneg : -((ν - μ) * (μ + ν)) / c ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hprod) hc2
  have hslope : Tendsto (slope (fractionalBarrierGap μ ν) c) (𝓝[<] c)
      (𝓝 (-((ν - μ) * (μ + ν)) / c ^ 2)) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hderiv
    exact h.mono_left (nhdsWithin_mono c (fun y hy => ne_of_lt hy))
  have hev_slope : ∀ᶠ y in 𝓝[<] c,
      slope (fractionalBarrierGap μ ν) c y < 0 :=
    hslope.eventually (eventually_lt_nhds hdneg)
  have hev_gt : ∀ᶠ y in 𝓝[<] c,
      fractionalBarrierGap μ ν c < fractionalBarrierGap μ ν y := by
    filter_upwards [hev_slope, self_mem_nhdsWithin] with y hsl hyc
    have hyc' : y - c < 0 := sub_neg.mpr hyc
    rw [slope_def_field] at hsl
    rcases div_neg_iff.mp hsl with ⟨hnum, hden⟩ | ⟨hnum, hden⟩
    · linarith [hnum]
    · linarith [hden, hyc']
  have hev_left : ∀ᶠ y in 𝓝[<] c, fractionalBarrierGap μ ν y < 0 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hsc')] with y hyc hsy
    exact hleft y hsy hyc
  have : ∃ y, fractionalBarrierGap μ ν c < fractionalBarrierGap μ ν y ∧
      fractionalBarrierGap μ ν y < 0 := (hev_gt.and hev_left).exists
  obtain ⟨y, hy1, hy2⟩ := this
  rw [htouch] at hy1
  linarith

/-- The endpoint `μ+ν=0`.  At this parameter the barrier gap solves a
homogeneous scalar linear ODE.  Backward uniqueness rules out contact with
zero after the explicit negative seed. -/
theorem besselRatioReal_fractional_upper_gt_neg_one_of_sum_eq_zero
    (μ ν : ℝ) (hμ : -1 < μ) (hμν : μ < ν) (hsum : μ + ν = 0)
    {x : ℝ} (hx : 0 < x) :
    besselRatioReal μ x - besselRatioReal ν x < (ν - μ) / x := by
  let G : ℝ → ℝ := fractionalBarrierGap μ ν
  set s := fractionalSeed μ ν with hs_def
  have hν : -1 < ν := lt_trans hμ hμν
  have hs0 : 0 < s := by
    simpa [hs_def] using fractionalSeed_pos μ ν hμ hμν
  have hsseed : G s < 0 := by
    simpa [G, hs_def] using fractionalBarrierGap_seed_gt_neg_one μ ν hμ hμν
  by_contra hcon
  push_neg at hcon
  have hxsgt : s < x := by
    by_contra hxs
    push_neg at hxs
    have hseed := fractionalBarrierGap_lt_of_le_seed μ ν hμ hμν hx (by
      simpa [hs_def] using hxs)
    unfold fractionalBarrierGap at hseed
    linarith
  have hcont : ContinuousOn G (Icc s x) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hs0 hy.1
    exact (fractionalBarrierGap_hasDerivAt_gt_neg_one μ ν hμ hμν hy0).continuousAt.continuousWithinAt
  have hzero_mem : (0 : ℝ) ∈ Icc (G s) (G x) := by
    constructor
    · exact hsseed.le
    · dsimp [G]
      unfold fractionalBarrierGap
      linarith
  rcases intermediate_value_Icc (le_of_lt hxsgt) hcont hzero_mem with
    ⟨c, hcI, hGc⟩
  have hsc : s ≤ c := hcI.1
  have hcx : c ≤ x := hcI.2
  have hc0 : 0 < c := lt_of_lt_of_le hs0 hsc
  let R : ℝ → ℝ := fun t => G (c - t)
  let Rp : ℝ → ℝ := fun t =>
    (besselRatioReal μ (c - t) + besselRatioReal ν (c - t) +
      1 / (c - t)) * G (c - t)
  let K : ℝ := c / (2 * (μ + 1)) + c / (2 * (ν + 1)) + 1 / s
  have hlen : 0 ≤ c - s := sub_nonneg.mpr hsc
  have hRcont : ContinuousOn R (Icc 0 (c - s)) := by
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    have hy0 : 0 < c - t := by linarith
    have hGcont := (fractionalBarrierGap_hasDerivAt_gt_neg_one
      μ ν hμ hμν hy0).continuousAt
    have hinner : ContinuousAt (fun z : ℝ => c - z) t :=
      continuousAt_const.sub continuousAt_id
    simpa [R, Function.comp_def] using
      (hGcont.comp hinner).continuousWithinAt
  have hRderiv : ∀ t ∈ Ico 0 (c - s),
      HasDerivWithinAt R (Rp t) (Ici t) t := by
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    have hy0 : 0 < c - t := by linarith
    have hG := fractionalBarrierGap_hasDerivAt_boundary μ ν hμ hμν hsum hy0
    have hinner : HasDerivAt (fun z : ℝ => c - z) (-1) t := by
      convert (hasDerivAt_const t c).sub (hasDerivAt_id t) using 1 <;> ring
    have hcomp := hG.comp t hinner
    convert hcomp.hasDerivWithinAt (s := Ici t) using 1 <;>
      simp only [R, Rp, G, Function.comp_apply] <;> ring
  have hRbound : ∀ t ∈ Ico 0 (c - s), ‖Rp t‖ ≤ K * ‖R t‖ := by
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    have hys : s < c - t := by linarith
    have hyc : c - t ≤ c := by linarith
    have hy0 : 0 < c - t := lt_trans hs0 hys
    have hρμ0 := besselRatioReal_pos_gt_neg_one hμ hy0
    have hρν0 := besselRatioReal_pos_gt_neg_one hν hy0
    have hρμ := besselRatioReal_lt_recurrence μ hμ hy0
    have hρν := besselRatioReal_lt_recurrence ν hν hy0
    have hμ1 : 0 < 2 * (μ + 1) := by linarith
    have hν1 : 0 < 2 * (ν + 1) := by linarith
    have hρμc : besselRatioReal μ (c - t) ≤ c / (2 * (μ + 1)) := by
      exact le_trans hρμ.le (div_le_div_of_nonneg_right hyc hμ1.le)
    have hρνc : besselRatioReal ν (c - t) ≤ c / (2 * (ν + 1)) := by
      exact le_trans hρν.le (div_le_div_of_nonneg_right hyc hν1.le)
    have hinv0 : 0 < 1 / (c - t) := one_div_pos.mpr hy0
    have hinv : 1 / (c - t) ≤ 1 / s := by
      exact one_div_le_one_div_of_le hs0 hys.le
    have hA0 : 0 ≤ besselRatioReal μ (c - t) +
        besselRatioReal ν (c - t) + 1 / (c - t) := by linarith
    have hAK : besselRatioReal μ (c - t) +
        besselRatioReal ν (c - t) + 1 / (c - t) ≤ K := by
      dsimp [K]
      linarith
    simp only [Rp, R, Real.norm_eq_abs, abs_mul, abs_of_nonneg hA0]
    exact mul_le_mul_of_nonneg_right hAK (abs_nonneg _)
  have hRzero : R 0 = 0 := by
    simpa [R] using hGc
  have hunique := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hRcont hRderiv hRzero hRbound (c - s) ⟨hlen, le_rfl⟩
  have hGs0 : G s = 0 := by
    simpa [R] using hunique
  linarith

/-- If `μ+ν<0`, the sharp barrier must fail somewhere.  This is proved
without asymptotics: recurrence bounds force `x²` times the gap to acquire
positive linear drift, contradicting a globally negative gap. -/
theorem exists_fractional_upper_failure_of_sum_neg
    (μ ν : ℝ) (hμ : -1 < μ) (hμν : μ < ν) (hsum : μ + ν < 0) :
    ∃ x : ℝ, 0 < x ∧
      (ν - μ) / x ≤ besselRatioReal μ x - besselRatioReal ν x := by
  let G : ℝ → ℝ := fractionalBarrierGap μ ν
  let F : ℝ := -((ν - μ) * (μ + ν))
  let H : ℝ → ℝ := fun y => y ^ 2 * G y
  let J : ℝ → ℝ := fun y => H y - F * y
  let X : ℝ := 12 * ((μ + 1) * (μ + 2) + (ν + 1) * (ν + 2) + 1)
  have hν : -1 < ν := lt_trans hμ hμν
  have hδ : 0 < ν - μ := sub_pos.mpr hμν
  have hF : 0 < F := by
    dsimp [F]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hδ hsum)
  have hX : 0 < X := by
    dsimp [X]
    have hμ1 : 0 < μ + 1 := by linarith
    have hμ2 : 0 < μ + 2 := by linarith
    have hν1 : 0 < ν + 1 := by linarith
    have hν2 : 0 < ν + 2 := by linarith
    positivity
  by_contra hnone
  push_neg at hnone
  have hGneg : ∀ y : ℝ, 0 < y → G y < 0 := by
    intro y hy
    have h := hnone y hy
    dsimp [G]
    unfold fractionalBarrierGap
    linarith
  have hJmono : MonotoneOn J (Ici X) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (𝕜 := ℝ) X)
    · intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le hX hy
      have hG' := fractionalBarrierGap_hasDerivAt_ode μ ν hμ hμν hy0
      have hG'' : HasDerivAt G
          (-(besselRatioReal μ y + besselRatioReal ν y + (μ + ν + 1) / y) *
              G y + F / y ^ 2) y := by
        convert hG' using 1 <;> simp [G, F] <;> ring
      have hH' := ((hasDerivAt_id y).pow 2).mul hG''
      have hFy' := (hasDerivAt_const y F).mul (hasDerivAt_id y)
      simpa [J, H] using (hH'.sub hFy').continuousAt.continuousWithinAt
    · intro y hy
      have hyX : X < y := by simpa [interior_Ici] using hy
      have hy0 : 0 < y := lt_trans hX hyX
      have hG' := fractionalBarrierGap_hasDerivAt_ode μ ν hμ hμν hy0
      have hG'' : HasDerivAt G
          (-(besselRatioReal μ y + besselRatioReal ν y + (μ + ν + 1) / y) *
              G y + F / y ^ 2) y := by
        convert hG' using 1 <;> simp [G, F] <;> ring
      have hH' := ((hasDerivAt_id y).pow 2).mul hG''
      have hFy' := (hasDerivAt_const y F).mul (hasDerivAt_id y)
      simpa [J, H] using
        (hH'.sub hFy').differentiableAt.differentiableWithinAt
    · intro y hy
      have hyX : X < y := by simpa [interior_Ici] using hy
      have hy0 : 0 < y := lt_trans hX hyX
      have hμlarge : 12 * (μ + 1) * (μ + 2) ≤ y ^ 2 := by
        dsimp [X] at hyX hX
        have hμ1 : 0 < μ + 1 := by linarith
        have hμ2 : 0 < μ + 2 := by linarith
        have hν1 : 0 < ν + 1 := by linarith
        have hν2 : 0 < ν + 2 := by linarith
        have hμA : 0 < (μ + 1) * (μ + 2) := mul_pos hμ1 hμ2
        have hνA : 0 < (ν + 1) * (ν + 2) := mul_pos hν1 hν2
        nlinarith
      have hνlarge : 12 * (ν + 1) * (ν + 2) ≤ y ^ 2 := by
        dsimp [X] at hyX hX
        have hμ1 : 0 < μ + 1 := by linarith
        have hμ2 : 0 < μ + 2 := by linarith
        have hν1 : 0 < ν + 1 := by linarith
        have hν2 : 0 < ν + 2 := by linarith
        have hμA : 0 < (μ + 1) * (μ + 2) := mul_pos hμ1 hμ2
        have hνA : 0 < (ν + 1) * (ν + 2) := mul_pos hν1 hν2
        nlinarith
      have hρμ := besselRatioReal_gt_three_halves μ hμ hy0 hμlarge
      have hρν := besselRatioReal_gt_three_halves ν hν hy0 hνlarge
      have hρμ' : 3 * (μ + 2) < 2 * y * besselRatioReal μ y := by
        rw [div_lt_iff₀ (by positivity : 0 < 2 * y)] at hρμ
        nlinarith
      have hρν' : 3 * (ν + 2) < 2 * y * besselRatioReal ν y := by
        rw [div_lt_iff₀ (by positivity : 0 < 2 * y)] at hρν
        nlinarith
      let A : ℝ := besselRatioReal μ y + besselRatioReal ν y +
        (μ + ν + 1) / y
      have hA : 2 / y < A := by
        rw [div_lt_iff₀ hy0]
        dsimp [A]
        field_simp [ne_of_gt hy0]
        nlinarith [hρμ', hρν']
      have hcoef : 2 * y - y ^ 2 * A < 0 := by
        rw [div_lt_iff₀ hy0] at hA
        nlinarith
      have hG' := fractionalBarrierGap_hasDerivAt_ode μ ν hμ hμν hy0
      have hG'' : HasDerivAt G (-A * G y + F / y ^ 2) y := by
        convert hG' using 1 <;> simp [G, F, A] <;> ring
      have hH' := ((hasDerivAt_id y).pow 2).mul hG''
      have hFy' := (hasDerivAt_const y F).mul (hasDerivAt_id y)
      have hJ' : HasDerivAt J ((2 * y - y ^ 2 * A) * G y) y := by
        convert hH'.sub hFy' using 1 <;>
          simp [J, H] <;> field_simp [ne_of_gt hy0] <;> ring
      rw [hJ'.deriv]
      exact (mul_pos_of_neg_of_neg hcoef (hGneg y hy0)).le
  let z : ℝ := X + (-H X) / F + 1
  have hGX := hGneg X hX
  have hHX : H X < 0 := by
    dsimp [H]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hX) hGX
  have hXz : X < z := by
    dsimp [z]
    have : 0 < (-H X) / F := div_pos (neg_pos.mpr hHX) hF
    linarith
  have hJle : J X ≤ J z := hJmono (by simp) (by simp [le_of_lt hXz]) (le_of_lt hXz)
  have hzrel : F * (z - X) = -H X + F := by
    dsimp [z]
    field_simp [ne_of_gt hF]
    ring
  have hHz : 0 < H z := by
    dsimp [J] at hJle
    nlinarith
  have hz0 : 0 < z := lt_trans hX hXz
  have hGz := hGneg z hz0
  have hHzneg : H z < 0 := by
    dsimp [H]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hz0) hGz
  linarith

/-- Exact classification of the sharp fractional barrier on `ν>-1`. -/
theorem besselRatioReal_fractional_upper_all_iff
    (μ ν : ℝ) (hμ : -1 < μ) (hμν : μ < ν) :
    (∀ x : ℝ, 0 < x →
      besselRatioReal μ x - besselRatioReal ν x < (ν - μ) / x) ↔
      0 ≤ μ + ν := by
  constructor
  · intro hall
    by_contra hsum
    push_neg at hsum
    obtain ⟨x, hx, hfail⟩ :=
      exists_fractional_upper_failure_of_sum_neg μ ν hμ hμν hsum
    linarith [hall x hx]
  · intro hsum x hx
    rcases hsum.eq_or_lt with hzero | hpos
    · exact besselRatioReal_fractional_upper_gt_neg_one_of_sum_eq_zero
        μ ν hμ hμν hzero.symm hx
    · exact besselRatioReal_fractional_upper_gt_neg_one_of_pos_sum
        μ ν hμ hμν hpos hx

/-- Optimal two-sided continuous-order estimate. -/
theorem besselRatioReal_fractional_two_sided
    (μ ν : ℝ) (hμ : -1 < μ) (hμν : μ < ν) (hsum : 0 ≤ μ + ν)
    {x : ℝ} (hx : 0 < x) :
    0 < besselRatioReal μ x - besselRatioReal ν x ∧
      besselRatioReal μ x - besselRatioReal ν x < (ν - μ) / x := by
  constructor
  · linarith [besselRatioReal_strictAnti_order μ ν hμ hμν hx]
  · exact (besselRatioReal_fractional_upper_all_iff μ ν hμ hμν).2 hsum x hx


end AmosClosure
