/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.AmosBoundProofReal

/-!
# The barrier at real order, and THE THEOREM (arc C4, phase 3c;
charter Amendment 5)

Near-literal port of the C3 first-crossing barrier: `ψ_ν > 2ν+1`
globally, hence **the Amos bound at every real order `ν ≥ 0`**
(`amosBoundReal_holds`), the real-order consumers, the SHORT
recovery of C3's integer theorem through the identification, and
the genuinely non-integer half-order witness.
-/

open Set Filter Topology

namespace AmosClosure

/-- **The global ψ theorem at real order**: `ψ_ν(x) > 2ν+1` for all
`x > 0`, by sInf first-crossing. -/
theorem besselPsiReal_gt (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    2 * ν + 1 < besselPsiReal ν x := by
  by_contra hcon
  push_neg at hcon
  have hx4 : (1 / 4 : ℝ) < x := by
    by_contra h4
    push_neg at h4
    exact absurd (besselPsiReal_zone ν hν hx h4) (not_lt.mpr hcon)
  -- the crossing set inside [1/4, x]
  set S := {y : ℝ | y ∈ Icc (1 / 4 : ℝ) x
    ∧ besselPsiReal ν y ≤ 2 * ν + 1} with hS_def
  have hSne : S.Nonempty := ⟨x, ⟨le_of_lt hx4, le_refl x⟩, hcon⟩
  have hSbdd : BddBelow S := ⟨1 / 4, fun y hy => hy.1.1⟩
  have hcont : ContinuousOn (besselPsiReal ν) (Icc (1 / 4 : ℝ) x) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy.1
    exact (besselPsiReal_hasDerivAt ν hν hy0).continuousAt.continuousWithinAt
  have hSclosed : IsClosed S := by
    have : S = Icc (1 / 4 : ℝ) x
        ∩ besselPsiReal ν ⁻¹' (Iic (2 * ν + 1)) := by
      ext y
      simp [hS_def, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    rw [this]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  set c := sInf S with hc_def
  have hcmem : c ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hc14 : (1 / 4 : ℝ) ≤ c := le_csInf hSne (fun y hy => hy.1.1)
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc14
  -- c ≠ 1/4 by the zone
  have hcne : c ≠ 1 / 4 := by
    intro h
    have := besselPsiReal_zone ν hν (by norm_num : (0 : ℝ) < 1 / 4)
      (le_refl _)
    rw [h] at hcmem
    exact absurd this (not_lt.mpr hcmem.2)
  have hc14' : (1 / 4 : ℝ) < c := lt_of_le_of_ne hc14 (Ne.symm hcne)
  -- left of c inside (1/4, c): ψ > 2ν+1 by minimality
  have hleft : ∀ y, 1 / 4 < y → y < c → 2 * ν + 1 < besselPsiReal ν y := by
    intro y h1 h2
    by_contra hy
    push_neg at hy
    have hymem : y ∈ S := by
      refine ⟨⟨le_of_lt h1, ?_⟩, hy⟩
      exact le_of_lt (lt_of_lt_of_le h2 (hcmem.1.2))
    exact absurd (csInf_le hSbdd hymem) (not_le.mpr h2)
  -- ψ(c) = 2ν+1 by left continuity
  have htendsto : Tendsto (besselPsiReal ν) (𝓝[<] c)
      (𝓝 (besselPsiReal ν c)) :=
    ((besselPsiReal_hasDerivAt ν hν hc0).continuousAt.continuousWithinAt)
  have hev_ge : ∀ᶠ y in 𝓝[<] c, 2 * ν + 1 ≤ besselPsiReal ν y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hc14')] with y hy1 hy2
    exact le_of_lt (hleft y hy2 hy1)
  have hpsi_ge : 2 * ν + 1 ≤ besselPsiReal ν c :=
    ge_of_tendsto htendsto hev_ge
  have htouch : besselPsiReal ν c = 2 * ν + 1 :=
    le_antisymm hcmem.2 hpsi_ge
  -- the derivative at the touch is (2ν+1)/c > 0
  have hQ0 := riccati_zero_of_real_touch hν hc0 htouch
  have hρc := besselRatioReal_pos hν hc0
  have hρc' : besselRatioReal ν c ≠ 0 := ne_of_gt hρc
  have hc' : c ≠ 0 := ne_of_gt hc0
  have heq : 1 / besselRatioReal ν c - besselRatioReal ν c
      = (2 * ν + 1) / c := by
    unfold besselPsiReal at htouch
    rw [eq_div_iff hc']
    nlinarith [htouch]
  have hψ' : HasDerivAt (besselPsiReal ν) ((2 * ν + 1) / c) c := by
    have h := besselPsiReal_hasDerivAt ν hν hc0
    rw [hQ0] at h
    convert h using 1
    rw [← heq]
    ring
  -- watchpoint (i): explicit numerator positivity from 0 ≤ ν
  have hnum : (0 : ℝ) < 2 * ν + 1 := by linarith
  have hd0 : (0 : ℝ) < (2 * ν + 1) / c := div_pos hnum hc0
  -- slope: eventually to the left, ψ y < ψ c
  have hslope : Tendsto (slope (besselPsiReal ν) c) (𝓝[<] c)
      (𝓝 ((2 * ν + 1) / c)) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hψ'
    exact h.mono_left (nhdsWithin_mono c (fun y hy => ne_of_lt hy))
  have hev_slope : ∀ᶠ y in 𝓝[<] c, 0 < slope (besselPsiReal ν) c y :=
    hslope.eventually (eventually_gt_nhds hd0)
  have hev_lt : ∀ᶠ y in 𝓝[<] c, besselPsiReal ν y < besselPsiReal ν c := by
    filter_upwards [hev_slope, self_mem_nhdsWithin] with y hsl hy
    have hyc : y - c < 0 := sub_neg.mpr hy
    have := hsl
    rw [slope_def_field] at this
    -- this : 0 < (ψ y − ψ c)/(y − c)   (slope f a b = (f b − f a)/(b − a))
    rcases div_pos_iff.mp this with ⟨hnum', hden⟩ | ⟨hnum', hden⟩
    · linarith [hden, hyc]
    · linarith [hnum']
  -- contradiction: just left of c, ψ < 2ν+1 AND ψ > 2ν+1
  have hev_gt : ∀ᶠ y in 𝓝[<] c, 2 * ν + 1 < besselPsiReal ν y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hc14')] with y hy1 hy2
    exact hleft y hy2 hy1
  have : ∃ y, besselPsiReal ν y < besselPsiReal ν c
      ∧ 2 * ν + 1 < besselPsiReal ν y :=
    (hev_lt.and hev_gt).exists
  obtain ⟨y, hy1, hy2⟩ := this
  rw [htouch] at hy1
  linarith

/-- **THE AMOS BOUND AT REAL ORDER** (arc C4 main result): for every
real `ν ≥ 0` and `x > 0`, the Γ-series Bessel ratio satisfies the
Amos upper bound.  No hypothesis beyond `0 ≤ ν` and `0 < x`. -/
theorem amosBoundReal_holds (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    AmosBound ν x (besselIReal (ν + 1) x / besselIReal ν x) := by
  have hψ := besselPsiReal_gt ν hν hx
  have hρ := besselRatioReal_pos hν hx
  have hB := amosRHS_pos_of_nonneg hν hx
  have hρ' : besselRatioReal ν x ≠ 0 := ne_of_gt hρ
  have hB' : amosRHS ν x ≠ 0 := ne_of_gt hB
  have hx' : x ≠ 0 := ne_of_gt hx
  have hcal := amosRHS_calibration_real hν hx
  -- ψ > 2ν+1  →  (1/ρ − ρ) > (2ν+1)/x = 1/B − B
  have h1 : (2 * ν + 1) / x
      < 1 / besselRatioReal ν x - besselRatioReal ν x := by
    rw [div_lt_iff₀ hx]
    unfold besselPsiReal at hψ
    nlinarith [hψ]
  have hgt : 1 / amosRHS ν x - amosRHS ν x
      < 1 / besselRatioReal ν x - besselRatioReal ν x := by
    rw [hcal]
    exact h1
  -- strict antitonicity of t ↦ 1/t − t on positives, algebraically
  have hexp : (1 / besselRatioReal ν x - besselRatioReal ν x
      - (1 / amosRHS ν x - amosRHS ν x))
      * (besselRatioReal ν x * amosRHS ν x)
      = (amosRHS ν x - besselRatioReal ν x)
        * (1 + besselRatioReal ν x * amosRHS ν x) := by
    field_simp
    ring
  have hprodpos : 0 < (amosRHS ν x - besselRatioReal ν x)
      * (1 + besselRatioReal ν x * amosRHS ν x) := by
    rw [← hexp]
    apply mul_pos
    · linarith [hgt]
    · exact mul_pos hρ hB
  have hfac2 : (0 : ℝ) < 1 + besselRatioReal ν x * amosRHS ν x := by
    linarith [mul_pos hρ hB]
  have hsub : 0 < amosRHS ν x - besselRatioReal ν x := by
    rcases mul_pos_iff.mp hprodpos with ⟨h, _⟩ | ⟨_, h2⟩
    · exact h
    · linarith [hfac2, h2]
  show besselIReal (ν + 1) x / besselIReal ν x < amosRHS ν x
  have : besselRatioReal ν x < amosRHS ν x := by linarith [hsub]
  exact this

/-! ### Consumers at real order -/

/-- Unit step at real order, unconditional. -/
theorem besselIReal_unit_step (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    besselIReal (ν + 1) x / besselIReal ν x
      - besselIReal (ν + 2) x / besselIReal (ν + 1) x < 1 / x :=
  unit_step_of_recurrence_and_amos x ν
    (besselIReal ν x) (besselIReal (ν + 1) x) (besselIReal (ν + 2) x)
    hx hν (besselIReal_pos ν hν hx)
    (besselIReal_pos (ν + 1) (by linarith) hx)
    (by rw [besselIReal_recurrence ν hν hx])
    (amosBoundReal_holds ν hν hx)

/-- Log-derivative monotonicity across real orders, in `deriv` form,
unconditional. -/
theorem besselIReal_logDeriv_lt (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    deriv (fun y => Real.log (besselIReal ν y)) x
      < deriv (fun y => Real.log (besselIReal (ν + 1) y)) x := by
  rw [(besselIReal_log_hasDerivAt ν hν hx).deriv,
    (besselIReal_log_hasDerivAt (ν + 1) (by linarith) hx).deriv]
  have h := logderiv_unit_step_increase x ν
    (besselIReal ν x) (besselIReal (ν + 1) x) (besselIReal (ν + 2) x)
    hx hν (besselIReal_pos ν hν hx)
    (besselIReal_pos (ν + 1) (by linarith) hx)
    (by rw [besselIReal_recurrence ν hν hx])
    (amosBoundReal_holds ν hν hx)
  rw [show ν + 1 + 1 = ν + 2 by ring]
  linarith [h]

/-! ### The two registered locks -/

/-- **RECOVERY LOCK** (charter: must be SHORT — a long chain here is
divergence evidence): C3's integer theorem re-derived through the
identification. -/
theorem amosBound_holds_recovered (n : ℕ) {x : ℝ} (hx : 0 < x) :
    AmosBound n x (besselI (n + 1) x / besselI n x) := by
  rw [← besselIReal_natCast n hx, ← besselIReal_natCast (n + 1) hx,
    show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
  exact amosBoundReal_holds (n : ℝ) (Nat.cast_nonneg n) hx

/-- **HALF-ORDER WITNESS** (charter: the endpoint must live outside
`Nat.cast`): the Amos bound at `ν = 1/2`. -/
theorem amosBoundReal_half_order {x : ℝ} (hx : 0 < x) :
    AmosBound (1 / 2 : ℝ) x
      (besselIReal (3 / 2) x / besselIReal (1 / 2) x) := by
  have h := amosBoundReal_holds (1 / 2 : ℝ) (by norm_num) hx
  rwa [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at h

end AmosClosure
