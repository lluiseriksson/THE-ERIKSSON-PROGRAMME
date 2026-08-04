/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.AmosBarrierReal

/-!
# Continuous-order comparison for the modified-Bessel ratio

For real `0 ≤ μ < ν`, this file proves the sharp upper comparison

`besselRatioReal μ x - besselRatioReal ν x < (ν - μ) / x`.

The proof is the two-flow Riccati argument.  The already verified Amos
bound supplies a small-`x` seed; at a hypothetical first contact with
the barrier, the derivative of the signed gap is

`-(ν - μ) * (μ + ν) / x² < 0`,

which has the wrong orientation for a first crossing from below.
-/

open Set Filter Topology

namespace AmosClosure

/-- Signed gap between the two real-order ratios and the sharp barrier. -/
noncomputable def fractionalBarrierGap (μ ν x : ℝ) : ℝ :=
  besselRatioReal μ x - besselRatioReal ν x - (ν - μ) / x

/-- Derivative of the signed fractional-order barrier gap. -/
lemma fractionalBarrierGap_hasDerivAt (μ ν : ℝ) (hμ : 0 ≤ μ) (hμν : μ < ν)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fractionalBarrierGap μ ν)
      (riccatiQReal μ x (besselRatioReal μ x)
        - riccatiQReal ν x (besselRatioReal ν x)
        + (ν - μ) / x ^ 2) x := by
  have hν : 0 ≤ ν := le_trans hμ (le_of_lt hμν)
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hμ' := besselRatioReal_hasDerivAt μ hμ hx
  have hν' := besselRatioReal_hasDerivAt ν hν hx
  have hb : HasDerivAt (fun y : ℝ => (ν - μ) / y) (-(ν - μ) / x ^ 2) x := by
    convert (hasDerivAt_const x (ν - μ)).div (hasDerivAt_id x) hx0 using 1
    simp only [id_eq]
    field_simp
    ring
  have h := (hμ'.sub hν').sub hb
  convert h using 1
  ring

/-- At a contact with the barrier, the signed gap has the exact negative
derivative required by the two-flow argument. -/
lemma fractionalBarrierGap_hasDerivAt_of_touch (μ ν : ℝ) (hμ : 0 ≤ μ)
    (hμν : μ < ν) {x : ℝ} (hx : 0 < x)
    (htouch : fractionalBarrierGap μ ν x = 0) :
    HasDerivAt (fractionalBarrierGap μ ν)
      (-((ν - μ) * (μ + ν)) / x ^ 2) x := by
  have h := fractionalBarrierGap_hasDerivAt μ ν hμ hμν hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hr : besselRatioReal μ x
      = besselRatioReal ν x + (ν - μ) / x := by
    unfold fractionalBarrierGap at htouch
    linarith
  convert h using 1
  unfold riccatiQReal
  rw [hr]
  field_simp [hx0]
  ring

/-- The Amos estimate gives a uniform small-argument seed below the
fractional barrier. -/
lemma fractionalBarrierGap_seed (μ ν : ℝ) (hμ : 0 ≤ μ) (hμν : μ < ν)
    {x : ℝ} (hx : 0 < x)
    (hxsmall : x ≤ min (1 / 4 : ℝ) ((ν - μ) / 2)) :
    fractionalBarrierGap μ ν x < 0 := by
  have hν : 0 ≤ ν := le_trans hμ (le_of_lt hμν)
  have hδ : 0 < ν - μ := sub_pos.mpr hμν
  have hx14 : x ≤ (1 / 4 : ℝ) := le_trans hxsmall (min_le_left _ _)
  have hxδ : x ≤ (ν - μ) / 2 := le_trans hxsmall (min_le_right _ _)
  have hmul : x * (x - 1 / 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hx.le (sub_nonpos.mpr hx14)
  have hxsq : x ^ 2 < ν - μ := by
    nlinarith
  have hρμ := besselRatioReal_pos hμ hx
  have hρν := besselRatioReal_pos hν hx
  have hamos := amosBoundReal_holds μ hμ hx
  have hsmall := amos_small μ x (besselRatioReal μ x) hμ hx hρμ hamos
  have hden : 0 < 2 * μ + 1 := by linarith
  have hρμx : besselRatioReal μ x < x := by
    have hdiv : x / (2 * μ + 1) ≤ x := by
      rw [div_le_iff₀ hden]
      nlinarith
    exact lt_of_lt_of_le hsmall hdiv
  have hxbarrier : x < (ν - μ) / x := by
    rw [lt_div_iff₀ hx]
    nlinarith
  unfold fractionalBarrierGap
  nlinarith

/-- **Continuous-order sharp upper comparison.**  For every pair of real
orders `0 ≤ μ < ν` and every positive argument, the ratio difference lies
strictly below `(ν - μ) / x`.

This is the fractional-step endpoint missing from the earlier unit-step
paper statement. -/
theorem besselRatioReal_fractional_upper (μ ν : ℝ) (hμ : 0 ≤ μ)
    (hμν : μ < ν) {x : ℝ} (hx : 0 < x) :
    besselRatioReal μ x - besselRatioReal ν x < (ν - μ) / x := by
  have hν : 0 ≤ ν := le_trans hμ (le_of_lt hμν)
  have hδ : 0 < ν - μ := sub_pos.mpr hμν
  set s : ℝ := min (1 / 4 : ℝ) ((ν - μ) / 2) with hs_def
  have hs0 : 0 < s := by
    rw [hs_def, lt_min_iff]
    constructor <;> linarith
  have hsseed : fractionalBarrierGap μ ν s < 0 := by
    apply fractionalBarrierGap_seed μ ν hμ hμν hs0
    rw [hs_def]
  by_contra hcon
  push_neg at hcon
  have hxsgt : s < x := by
    by_contra hxs
    push_neg at hxs
    have := fractionalBarrierGap_seed μ ν hμ hμν hx hxs
    unfold fractionalBarrierGap at this
    linarith
  set S := {y : ℝ | y ∈ Icc s x ∧ 0 ≤ fractionalBarrierGap μ ν y}
    with hS_def
  have hSne : S.Nonempty := by
    refine ⟨x, ⟨le_of_lt hxsgt, le_refl x⟩, ?_⟩
    unfold fractionalBarrierGap
    linarith
  have hSbdd : BddBelow S := ⟨s, fun y hy => hy.1.1⟩
  have hcont : ContinuousOn (fractionalBarrierGap μ ν) (Icc s x) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hs0 hy.1
    exact (fractionalBarrierGap_hasDerivAt μ ν hμ hμν hy0).continuousAt.continuousWithinAt
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
    ((fractionalBarrierGap_hasDerivAt μ ν hμ hμν hc0).continuousAt.continuousWithinAt)
  have hev_le : ∀ᶠ y in 𝓝[<] c, fractionalBarrierGap μ ν y ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hsc')] with y hyc hsy
    exact le_of_lt (hleft y hsy hyc)
  have hgap_le : fractionalBarrierGap μ ν c ≤ 0 :=
    le_of_tendsto htendsto hev_le
  have htouch : fractionalBarrierGap μ ν c = 0 :=
    le_antisymm hgap_le hcmem.2
  have hderiv := fractionalBarrierGap_hasDerivAt_of_touch μ ν hμ hμν hc0 htouch
  have hsum : 0 < μ + ν := by linarith
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
  have : ∃ y, fractionalBarrierGap μ ν c < fractionalBarrierGap μ ν y
      ∧ fractionalBarrierGap μ ν y < 0 := (hev_gt.and hev_left).exists
  obtain ⟨y, hy1, hy2⟩ := this
  rw [htouch] at hy1
  linarith

/-- Logarithmic derivatives increase strictly across arbitrary real orders
on the nonnegative order axis. -/
theorem besselIReal_logDeriv_fractional_lt (μ ν : ℝ) (hμ : 0 ≤ μ)
    (hμν : μ < ν) {x : ℝ} (hx : 0 < x) :
    deriv (fun y => Real.log (besselIReal μ y)) x
      < deriv (fun y => Real.log (besselIReal ν y)) x := by
  rw [(besselIReal_log_hasDerivAt μ hμ hx).deriv,
    (besselIReal_log_hasDerivAt ν (le_trans hμ (le_of_lt hμν)) hx).deriv]
  have hupper := besselRatioReal_fractional_upper μ ν hμ hμν hx
  unfold besselRatioReal at hupper
  have hx0 : x ≠ 0 := ne_of_gt hx
  calc
    besselIReal (μ + 1) x / besselIReal μ x + μ / x
        = μ / x + besselIReal (μ + 1) x / besselIReal μ x := by ring
    _ < μ / x + ((ν - μ) / x + besselIReal (ν + 1) x / besselIReal ν x) :=
      add_lt_add_right ((sub_lt_iff_lt_add).mp hupper) _
    _ = besselIReal (ν + 1) x / besselIReal ν x + ν / x := by
      field_simp [hx0]
      ring

end AmosClosure
