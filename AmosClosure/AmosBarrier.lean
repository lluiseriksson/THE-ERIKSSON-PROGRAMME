/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.AmosBoundProof

/-!
# The barrier, and the Amos bound as a theorem (arc C3, phase 2b)

At any `c > 0` with `ψ_n(c) = 2n+1`, the Riccati equation forces
`ρ'(c) = 0` (substituting `(2n+1)/c = 1/ρ − ρ` into the quadratic
annihilates it), so `ψ'(c) = (2n+1)/c > 0`: every touch of the level
`2n+1` is an upward crossing.  Combined with the zone theorem
(`ψ > 2n+1` on `(0, 1/4]`) and an `sInf` first-crossing argument,
`ψ_n > 2n+1` on all of `(0, ∞)`; the strict antitonicity of
`t ↦ 1/t − t` then converts this into the Amos bound
`ρ_n(x) < amosRHS n x` — **the bound is a theorem**, and every
consumer of the lane becomes unconditional over `besselI`.
-/

open Set Filter Topology

namespace AmosClosure

/-- At a touch point `ψ(c) = 2n+1`, the Riccati value vanishes. -/
lemma riccati_zero_of_touch (n : ℕ) {c : ℝ} (hc : 0 < c)
    (htouch : besselPsi n c = 2 * (n : ℝ) + 1) :
    riccatiQ n c (besselRatio n c) = 0 := by
  have hρ := besselRatio_pos n hc
  have hρ' : besselRatio n c ≠ 0 := ne_of_gt hρ
  have hc' : c ≠ 0 := ne_of_gt hc
  have heq : 1 / besselRatio n c - besselRatio n c
      = (2 * (n : ℝ) + 1) / c := by
    unfold besselPsi at htouch
    rw [eq_div_iff hc']
    nlinarith [htouch]
  unfold riccatiQ
  rw [← heq]
  field_simp
  ring

/-- **The global ψ theorem**: `ψ_n(x) > 2n+1` for all `x > 0`. -/
theorem besselPsi_gt (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (2 * (n : ℝ) + 1) < besselPsi n x := by
  by_contra hcon
  push_neg at hcon
  have hx4 : (1 / 4 : ℝ) < x := by
    by_contra h4
    push_neg at h4
    exact absurd (besselPsi_zone n hx h4) (not_lt.mpr hcon)
  -- the crossing set inside [1/4, x]
  set S := {y : ℝ | y ∈ Icc (1 / 4 : ℝ) x
    ∧ besselPsi n y ≤ 2 * (n : ℝ) + 1} with hS_def
  have hSsub : S ⊆ Icc (1 / 4 : ℝ) x := fun y hy => hy.1
  have hSne : S.Nonempty := ⟨x, ⟨le_of_lt hx4, le_refl x⟩, hcon⟩
  have hSbdd : BddBelow S := ⟨1 / 4, fun y hy => hy.1.1⟩
  have hcont : ContinuousOn (besselPsi n) (Icc (1 / 4 : ℝ) x) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy.1
    exact (besselPsi_hasDerivAt n hy0).continuousAt.continuousWithinAt
  have hSclosed : IsClosed S := by
    have : S = Icc (1 / 4 : ℝ) x
        ∩ besselPsi n ⁻¹' (Iic (2 * (n : ℝ) + 1)) := by
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
    have := besselPsi_zone n (by norm_num : (0:ℝ) < 1/4) (le_refl _)
    rw [h] at hcmem
    exact absurd this (not_lt.mpr hcmem.2)
  have hc14' : (1 / 4 : ℝ) < c := lt_of_le_of_ne hc14 (Ne.symm hcne)
  -- left of c inside [1/4, c): ψ > 2n+1
  have hleft : ∀ y, 1 / 4 < y → y < c → (2 * (n : ℝ) + 1) < besselPsi n y := by
    intro y h1 h2
    by_contra hy
    push_neg at hy
    have hymem : y ∈ S := by
      refine ⟨⟨le_of_lt h1, ?_⟩, hy⟩
      exact le_of_lt (lt_of_lt_of_le h2 (hcmem.1.2))
    exact absurd (csInf_le hSbdd hymem) (not_le.mpr h2)
  -- ψ(c) = 2n+1 by left continuity
  have htendsto : Tendsto (besselPsi n) (𝓝[<] c) (𝓝 (besselPsi n c)) :=
    ((besselPsi_hasDerivAt n hc0).continuousAt.continuousWithinAt)
  have hev_ge : ∀ᶠ y in 𝓝[<] c, (2 * (n : ℝ) + 1) ≤ besselPsi n y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hc14')] with y hy1 hy2
    exact le_of_lt (hleft y hy2 hy1)
  have hpsi_ge : (2 * (n : ℝ) + 1) ≤ besselPsi n c :=
    ge_of_tendsto htendsto hev_ge
  have htouch : besselPsi n c = 2 * (n : ℝ) + 1 :=
    le_antisymm hcmem.2 hpsi_ge
  -- the derivative at the touch is (2n+1)/c > 0
  have hQ0 := riccati_zero_of_touch n hc0 htouch
  have hρc := besselRatio_pos n hc0
  have hρc' : besselRatio n c ≠ 0 := ne_of_gt hρc
  have hc' : c ≠ 0 := ne_of_gt hc0
  have heq : 1 / besselRatio n c - besselRatio n c
      = (2 * (n : ℝ) + 1) / c := by
    unfold besselPsi at htouch
    rw [eq_div_iff hc']
    nlinarith [htouch]
  have hψ' : HasDerivAt (besselPsi n) ((2 * (n : ℝ) + 1) / c) c := by
    have h := besselPsi_hasDerivAt n hc0
    rw [hQ0] at h
    convert h using 1
    rw [← heq]
    ring
  have hd0 : (0 : ℝ) < (2 * (n : ℝ) + 1) / c := by positivity
  -- slope: eventually to the left, ψ y < ψ c
  have hslope : Tendsto (slope (besselPsi n) c) (𝓝[<] c)
      (𝓝 ((2 * (n : ℝ) + 1) / c)) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hψ'
    exact h.mono_left (nhdsWithin_mono c (fun y hy => ne_of_lt hy))
  have hev_slope : ∀ᶠ y in 𝓝[<] c, 0 < slope (besselPsi n) c y :=
    hslope.eventually (eventually_gt_nhds hd0)
  have hev_lt : ∀ᶠ y in 𝓝[<] c, besselPsi n y < besselPsi n c := by
    filter_upwards [hev_slope, self_mem_nhdsWithin] with y hsl hy
    have hyc : y - c < 0 := sub_neg.mpr hy
    have := hsl
    rw [slope_def_field] at this
    -- this : 0 < (ψ y − ψ c)/(y − c) — wait slope_def_field: slope f a b = (f b − f a)/(b − a)
    rcases div_pos_iff.mp this with ⟨hnum, hden⟩ | ⟨hnum, hden⟩
    · linarith [hden, hyc]
    · linarith [hnum]
  -- contradiction: just left of c, ψ < 2n+1 AND ψ > 2n+1
  have hev_gt : ∀ᶠ y in 𝓝[<] c, (2 * (n : ℝ) + 1) < besselPsi n y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hc14')] with y hy1 hy2
    exact hleft y hy2 hy1
  have : ∃ y, besselPsi n y < besselPsi n c
      ∧ (2 * (n : ℝ) + 1) < besselPsi n y :=
    (hev_lt.and hev_gt).exists
  obtain ⟨y, hy1, hy2⟩ := this
  rw [htouch] at hy1
  linarith

/-- **THE AMOS BOUND, AS A THEOREM** (arc C3 main result): for every
integer order `n` and `x > 0`, the true series-Bessel ratio satisfies
the Amos upper bound.  No hypothesis remains. -/
theorem amosBound_holds (n : ℕ) {x : ℝ} (hx : 0 < x) :
    AmosBound n x (besselI (n + 1) x / besselI n x) := by
  have hψ := besselPsi_gt n hx
  have hρ := besselRatio_pos n hx
  have hB := amosRHS_pos n hx
  have hρ' : besselRatio n x ≠ 0 := ne_of_gt hρ
  have hB' : amosRHS n x ≠ 0 := ne_of_gt hB
  have hx' : x ≠ 0 := ne_of_gt hx
  have hcal := amosRHS_calibration n hx
  -- ψ > 2n+1  →  (1/ρ − ρ) > (2n+1)/x = 1/B − B
  have h1 : (2 * (n : ℝ) + 1) / x
      < 1 / besselRatio n x - besselRatio n x := by
    rw [div_lt_iff₀ hx]
    unfold besselPsi at hψ
    nlinarith [hψ]
  have hgt : 1 / amosRHS n x - amosRHS n x
      < 1 / besselRatio n x - besselRatio n x := by
    rw [hcal]
    exact h1
  -- strict antitonicity of t ↦ 1/t − t on positives
  have hexp : (1 / besselRatio n x - besselRatio n x
      - (1 / amosRHS n x - amosRHS n x))
      * (besselRatio n x * amosRHS n x)
      = (amosRHS n x - besselRatio n x)
        * (1 + besselRatio n x * amosRHS n x) := by
    field_simp
    ring
  have hprodpos : 0 < (amosRHS n x - besselRatio n x)
      * (1 + besselRatio n x * amosRHS n x) := by
    rw [← hexp]
    apply mul_pos
    · linarith [hgt]
    · exact mul_pos hρ hB
  have hfac2 : (0 : ℝ) < 1 + besselRatio n x * amosRHS n x := by
    positivity
  have hsub : 0 < amosRHS n x - besselRatio n x := by
    rcases mul_pos_iff.mp hprodpos with ⟨h, _⟩ | ⟨_, h2⟩
    · exact h
    · linarith [hfac2, h2]
  show besselI (n + 1) x / besselI n x < amosRHS n x
  have : besselRatio n x < amosRHS n x := by linarith [hsub]
  exact this

/-! ### Every consumer, unconditional -/

/-- Unit step, unconditional. -/
theorem besselI_unit_step_unconditional (n : ℕ) {x : ℝ} (hx : 0 < x) :
    besselI (n + 1) x / besselI n x
      - besselI (n + 2) x / besselI (n + 1) x < 1 / x :=
  besselI_unit_step n hx (amosBound_holds n hx)

/-- Log-derivative monotonicity in `deriv` form, unconditional. -/
theorem besselI_logDeriv_lt_unconditional (n : ℕ) {x : ℝ} (hx : 0 < x) :
    deriv (fun y => Real.log (besselI n y)) x
      < deriv (fun y => Real.log (besselI (n + 1) y)) x :=
  besselI_logDeriv_lt n hx (amosBound_holds n hx)

/-- φ-monotonicity step, unconditional. -/
theorem besselI_phi_step_unconditional (m : ℕ) {x : ℝ} (hx : 0 < x) :
    (((m : ℝ) + 1 - 1) / (besselI (m + 1) x / besselI m x) ^ 2
        + ((m : ℝ) + 1 + 1) * (besselI (m + 2) x / besselI (m + 1) x) ^ 2)
      / ((m : ℝ) + 1)
    < (((m : ℝ) + 1) / (besselI (m + 2) x / besselI (m + 1) x) ^ 2
        + ((m : ℝ) + 1 + 2) * (besselI (m + 3) x / besselI (m + 2) x) ^ 2)
      / ((m : ℝ) + 1 + 1) := by
  apply besselI_phi_step m hx
  have h := amosBound_holds (m + 1) hx
  have e : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [show (m : ℝ) + 1 = (((m + 1 : ℕ)) : ℝ) from e.symm]
  exact h

end AmosClosure
