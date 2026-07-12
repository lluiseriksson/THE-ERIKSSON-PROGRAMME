/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.AmosCrossing

/-!
# Phase 3F: exclusion of the degenerate critical contact
(arc C5; charter Amendments 5–6)

At the threshold `x_†` the crossing-slope factor vanishes
IDENTICALLY, so a contact there is automatically a critical point
of `D = ρ − B_c`.  There the square root collapses —
`√(a²+x²) = a/t` exactly, `a = ν+c`, `t = 2c−1` — turning the
second-order data into rational algebra with the single relation
`x² = a²(1−t²)/t²`.  The registered identity
`D″(x_†) = t³·B/a² > 0` (external desk, probe-confirmed 90/90)
then forces `D` to be strictly decreasing on a left interval, so
`D > 0` just left of the contact — contradicting
`crossing_orientation_below`, which pins `D < 0` strictly below
the threshold.  CONSEQUENCES: the threshold inequality is STRICT
at every crossing, and uniqueness/orientation become
UNCONDITIONAL.
-/

open Set Filter Topology

namespace AmosClosure

/-- The derivative-value function of the crossing difference:
`D′(y) = Q_y(ρ(y)) − B′(y)`. -/
noncomputable def crossingDeriv (ν c y : ℝ) : ℝ :=
  riccatiQReal ν y (besselIReal (ν + 1) y / besselIReal ν y)
    - (ν + c) / (Real.sqrt ((ν + c) ^ 2 + y ^ 2)
        * (ν + c + Real.sqrt ((ν + c) ^ 2 + y ^ 2)))

/-- `D` has derivative `crossingDeriv` at every positive point. -/
lemma crossing_hasDerivAt_everywhere (ν : ℝ) (hν : 0 ≤ ν) (c : ℝ)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z => besselIReal (ν + 1) z / besselIReal ν z
        - amosFamily ν c z)
      (crossingDeriv ν c y) y :=
  (besselRatioReal_hasDerivAt ν hν hy).sub (amosFamily_hasDerivAt ν c hy)

/-- **EXCLUSION OF THE DEGENERATE CRITICAL CONTACT** (phase 3F):
no crossing can occur exactly at the threshold. -/
theorem crossing_no_critical_contact (ν : ℝ) (hν : 0 ≤ ν) {c x : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) (hx : 0 < x)
    (heq : besselIReal (ν + 1) x / besselIReal ν x = amosFamily ν c x)
    (hcrit : ν + c = (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + x ^ 2)) :
    False := by
  have ht : (0 : ℝ) < 2 * c - 1 := by linarith
  have ha : (0 : ℝ) < ν + c := by linarith
  have hupos : (0 : ℝ) < (ν + c) ^ 2 + x ^ 2 := by positivity
  have hS0 : 0 < Real.sqrt ((ν + c) ^ 2 + x ^ 2) := Real.sqrt_pos.mpr hupos
  -- the square root collapses at the contact
  have hs_val : Real.sqrt ((ν + c) ^ 2 + x ^ 2) = (ν + c) / (2 * c - 1) := by
    rw [eq_div_iff (ne_of_gt ht)]
    linarith [hcrit]
  have hs2 := Real.sq_sqrt hupos.le
  rw [hs_val] at hs2
  -- hs2 : ((ν+c)/(2c−1))² = (ν+c)² + x²  — the single relation
  have hx2_eq : x ^ 2 * (2 * c - 1) ^ 2
      = (ν + c) ^ 2 * (1 - (2 * c - 1) ^ 2) := by
    have h := hs2
    rw [div_pow, div_eq_iff (by positivity : ((2 * c - 1) : ℝ) ^ 2 ≠ 0)] at h
    linear_combination -h
  -- B collapses to a rational value
  have hB_val : amosFamily ν c x = x * (2 * c - 1) / (2 * c * (ν + c)) := by
    unfold amosFamily
    rw [hs_val]
    rw [div_eq_div_iff (by
      have : (0:ℝ) < (ν + c) / (2*c-1) := div_pos ha ht
      linarith) (by nlinarith [ha, hc1])]
    field_simp
    ring
  have hBpos := amosFamily_pos ν c hx
  -- ρ and Q at the contact
  have hQ0 : riccatiQReal ν x (besselIReal (ν + 1) x / besselIReal ν x)
      = (2 * c - 1) / x * amosFamily ν c x := by
    rw [heq]
    exact riccatiQReal_amosFamily ν c hx
  -- D′(x) = 0 at the critical contact
  have hD1x : crossingDeriv ν c x = 0 := by
    unfold crossingDeriv
    rw [hQ0, hs_val, hB_val]
    field_simp
    ring
  -- second derivative: assemble HasDerivAt of crossingDeriv at x
  -- piece A: y ↦ Q_y(ρ y)
  have hρ := besselRatioReal_hasDerivAt ν hν hx
  set ρx := besselIReal (ν + 1) x / besselIReal ν x with hρx_def
  set Q0 := riccatiQReal ν x ρx with hQ0_def
  have hg : HasDerivAt (fun y : ℝ => (2 * ν + 1) / y)
      ((0 * x - (2 * ν + 1) * 1) / x ^ 2) x :=
    (hasDerivAt_const x (2 * ν + 1)).div (hasDerivAt_id x) (ne_of_gt hx)
  have hA : HasDerivAt (fun y => riccatiQReal ν y
      (besselIReal (ν + 1) y / besselIReal ν y))
      ((2 * ν + 1) / x ^ 2 * ρx - ((2 * ν + 1) / x + 2 * ρx) * Q0) x := by
    have hmul := hg.mul hρ
    have hpow := hρ.pow 2
    have hassemble := ((hasDerivAt_const x (1 : ℝ)).sub hmul).sub hpow
    convert hassemble using 1
    have hR : besselRatioReal ν x = ρx := rfl
    have hQr : riccatiQReal ν x ρx = Q0 := rfl
    rw [hR, hQr]
    push_cast
    ring
  -- piece B: y ↦ B′(y) = a/(S(y)·(a+S(y)))
  have hinner : HasDerivAt (fun y : ℝ => (ν + c) ^ 2 + y ^ 2) (2 * x) x := by
    have h := (hasDerivAt_pow 2 x).const_add ((ν + c) ^ 2)
    simpa using h
  have hsqrt : HasDerivAt (fun y => Real.sqrt ((ν + c) ^ 2 + y ^ 2))
      (2 * x / (2 * Real.sqrt ((ν + c) ^ 2 + x ^ 2))) x :=
    hinner.sqrt (ne_of_gt hupos)
  set S := Real.sqrt ((ν + c) ^ 2 + x ^ 2) with hS_def
  have hprod : HasDerivAt
      (fun y => Real.sqrt ((ν + c) ^ 2 + y ^ 2)
        * (ν + c + Real.sqrt ((ν + c) ^ 2 + y ^ 2)))
      (2 * x / (2 * S) * (ν + c + S) + S * (2 * x / (2 * S))) x := by
    have h2 : HasDerivAt
        (fun y => ν + c + Real.sqrt ((ν + c) ^ 2 + y ^ 2))
        (2 * x / (2 * S)) x := by
      simpa using hsqrt.const_add (ν + c)
    exact hsqrt.mul h2
  have hSprod_pos : 0 < S * (ν + c + S) := by
    apply mul_pos hS0
    linarith [hS0, ha]
  have hB1 : HasDerivAt (fun y => (ν + c)
      / (Real.sqrt ((ν + c) ^ 2 + y ^ 2)
        * (ν + c + Real.sqrt ((ν + c) ^ 2 + y ^ 2))))
      ((0 * (S * (ν + c + S)) - (ν + c)
          * (2 * x / (2 * S) * (ν + c + S) + S * (2 * x / (2 * S))))
        / (S * (ν + c + S)) ^ 2) x :=
    (hasDerivAt_const x (ν + c)).div hprod (ne_of_gt hSprod_pos)
  have hV : HasDerivAt (crossingDeriv ν c)
      (((2 * ν + 1) / x ^ 2 * ρx - ((2 * ν + 1) / x + 2 * ρx) * Q0)
        - ((0 * (S * (ν + c + S)) - (ν + c)
            * (2 * x / (2 * S) * (ν + c + S) + S * (2 * x / (2 * S))))
          / (S * (ν + c + S)) ^ 2)) x := hA.sub hB1
  -- positivity of the second derivative at the contact
  have hVpos : 0 < ((2 * ν + 1) / x ^ 2 * ρx - ((2 * ν + 1) / x + 2 * ρx) * Q0)
      - ((0 * (S * (ν + c + S)) - (ν + c)
          * (2 * x / (2 * S) * (ν + c + S) + S * (2 * x / (2 * S))))
        / (S * (ν + c + S)) ^ 2) := by
    rw [heq, hQ0, hs_val, hB_val]
    have hc0 : (0 : ℝ) < 2 * c := by linarith
    have hval : (2 * ν + 1) / x ^ 2 * (x * (2 * c - 1) / (2 * c * (ν + c)))
        - ((2 * ν + 1) / x + 2 * (x * (2 * c - 1) / (2 * c * (ν + c))))
          * ((2 * c - 1) / x * (x * (2 * c - 1) / (2 * c * (ν + c))))
        - (0 * ((ν + c) / (2 * c - 1)
              * (ν + c + (ν + c) / (2 * c - 1)))
            - (ν + c) * (2 * x / (2 * ((ν + c) / (2 * c - 1)))
                * (ν + c + (ν + c) / (2 * c - 1))
              + (ν + c) / (2 * c - 1)
                * (2 * x / (2 * ((ν + c) / (2 * c - 1))))))
          / ((ν + c) / (2 * c - 1)
              * (ν + c + (ν + c) / (2 * c - 1))) ^ 2
        = (2 * c - 1) ^ 3 * (x * (2 * c - 1) / (2 * c * (ν + c)))
            / (ν + c) ^ 2 := by
      field_simp
      linear_combination (-2 * c ^ 2 * (2 * ν + 1)) * hx2_eq
    rw [hval]
    have hBnum : (0 : ℝ) < x * (2 * c - 1) / (2 * c * (ν + c)) := by
      apply div_pos (mul_pos hx ht)
      positivity
    positivity
  -- slope dance on crossingDeriv: it is negative on a left interval
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hV).mono_left
    (nhdsWithin_mono x (fun y (hy : y ∈ Set.Iio x) => ne_of_lt hy))
  have hev_slope : ∀ᶠ y in 𝓝[<] x, 0 < slope (crossingDeriv ν c) x y :=
    hslope.eventually (eventually_gt_nhds hVpos)
  have hev_neg : ∀ᶠ y in 𝓝[<] x, crossingDeriv ν c y < 0 := by
    filter_upwards [hev_slope, self_mem_nhdsWithin] with y hsl hy
    rw [slope_def_field, hD1x, sub_zero] at hsl
    have hyx : y - x < 0 := sub_neg.mpr hy
    rcases div_pos_iff.mp hsl with ⟨_, hden⟩ | ⟨hnum, _⟩
    · linarith [hden, hyx]
    · linarith [hnum]
  -- extract a concrete left interval
  obtain ⟨v, hvmem, hvsub⟩ := hev_neg.exists_mem
  rw [mem_nhdsWithin] at hvmem
  obtain ⟨U, hUopen, hxU, hUsub⟩ := hvmem
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen x hxU
  set y₁ := x - min (ε / 2) (x / 2) with hy₁_def
  have hmin : 0 < min (ε / 2) (x / 2) := lt_min (by linarith) (by linarith)
  have hy₁x : y₁ < x := by rw [hy₁_def]; linarith
  have hy₁0 : 0 < y₁ := by
    rw [hy₁_def]
    have : min (ε / 2) (x / 2) ≤ x / 2 := min_le_right _ _
    linarith
  have hIoo : Set.Ioo y₁ x ⊆ {y | crossingDeriv ν c y < 0} := by
    intro z hz
    apply hvsub
    apply hUsub
    constructor
    · apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have h1 : min (ε / 2) (x / 2) ≤ ε / 2 := min_le_left _ _
        have := hz.1
        rw [hy₁_def] at this
        linarith
      · linarith [hz.2, hε]
    · exact hz.2
  -- D strictly decreasing on [y₁, x] ⇒ D y₁ > D x = 0
  have hDanti : StrictAntiOn
      (fun z => besselIReal (ν + 1) z / besselIReal ν z - amosFamily ν c z)
      (Set.Icc y₁ x) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc y₁ x)
    · intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le hy₁0 hz.1
      exact ((crossing_hasDerivAt_everywhere ν hν c hz0).continuousAt).continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := lt_trans hy₁0 hz.1
      rw [(crossing_hasDerivAt_everywhere ν hν c hz0).deriv]
      exact hIoo hz
  have hDx0 : besselIReal (ν + 1) x / besselIReal ν x - amosFamily ν c x = 0 := by
    linarith [heq]
  have hDy₁pos : 0 < besselIReal (ν + 1) y₁ / besselIReal ν y₁
      - amosFamily ν c y₁ := by
    have h := hDanti (Set.left_mem_Icc.mpr (le_of_lt hy₁x))
      (Set.right_mem_Icc.mpr (le_of_lt hy₁x)) hy₁x
    simpa [hDx0] using h
  -- but y₁ is strictly below the threshold, so D y₁ < 0
  have hsy₁ : Real.sqrt ((ν + c) ^ 2 + y₁ ^ 2)
      < Real.sqrt ((ν + c) ^ 2 + x ^ 2) := by
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith [hy₁x, hy₁0]
  have hbelow : (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + y₁ ^ 2) < ν + c := by
    calc (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + y₁ ^ 2)
        < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + x ^ 2) :=
          mul_lt_mul_of_pos_left hsy₁ ht
      _ = ν + c := hcrit.symm
  have hDy₁neg := crossing_orientation_below ν hν hc1 hc2 hy₁0 hbelow
  linarith [hDy₁pos, hDy₁neg]

/-- **STRICT THRESHOLD** (3F corollary): every crossing satisfies
the strict inequality. -/
theorem crossing_threshold_strict (ν : ℝ) (hν : 0 ≤ ν) {c x : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) (hx : 0 < x)
    (heq : besselIReal (ν + 1) x / besselIReal ν x = amosFamily ν c x) :
    ν + c < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + x ^ 2) := by
  rcases lt_or_eq_of_le (crossing_threshold ν hν hc1 hc2 hx heq) with h | h
  · exact h
  · exact absurd (crossing_no_critical_contact ν hν hc1 hc2 hx heq h)
      not_false

/-- **UNCONDITIONAL UNIQUENESS** (3F corollary): any two crossings
coincide — no threshold hypotheses. -/
theorem crossing_unique_unconditional (ν : ℝ) (hν : 0 ≤ ν)
    {c x₁ x₂ : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (heq₁ : besselIReal (ν + 1) x₁ / besselIReal ν x₁ = amosFamily ν c x₁)
    (heq₂ : besselIReal (ν + 1) x₂ / besselIReal ν x₂ = amosFamily ν c x₂) :
    x₁ = x₂ :=
  crossing_unique ν hν hc1 hc2 hx₁ hx₂ heq₁ heq₂
    (crossing_threshold_strict ν hν hc1 hc2 hx₁ heq₁)
    (crossing_threshold_strict ν hν hc1 hc2 hx₂ heq₂)

/-- **THE GLOBAL CROSSING THEOREM** (arc C5 main result,
unconditional): for every real `ν ≥ 0` and `1/2 < c < 1` there is a
UNIQUE `x_* > 0` where the ratio meets `B_{ν,c}`; strictly below it
the ratio is below, strictly above it the ratio is above; and the
crossing obeys the explicit two-sided scale law. -/
theorem amosFamily_global_crossing (ν : ℝ) (hν : 0 ≤ ν) {c : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) :
    ∃! x : ℝ, 0 < x
      ∧ besselIReal (ν + 1) x / besselIReal ν x = amosFamily ν c x := by
  obtain ⟨x, hx, heq, _, _⟩ := crossing_scale ν hν hc1 hc2
  refine ⟨x, ⟨hx, heq⟩, ?_⟩
  rintro y ⟨hy, heqy⟩
  exact crossing_unique_unconditional ν hν hc1 hc2 hy hx heqy heq

/-- Full orientation at the unique crossing, unconditional. -/
theorem amosFamily_crossing_orientation (ν : ℝ) (hν : 0 ≤ ν)
    {c x y : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1) (hx : 0 < x)
    (heq : besselIReal (ν + 1) x / besselIReal ν x = amosFamily ν c x)
    (hy : 0 < y) :
    (y < x → besselIReal (ν + 1) y / besselIReal ν y < amosFamily ν c y)
      ∧ (x < y →
        amosFamily ν c y < besselIReal (ν + 1) y / besselIReal ν y) := by
  constructor
  · intro hyx
    rcases lt_trichotomy (besselIReal (ν + 1) y / besselIReal ν y)
      (amosFamily ν c y) with h | h | h
    · exact h
    · exact absurd (crossing_unique_unconditional ν hν hc1 hc2 hy hx h heq)
        (ne_of_lt hyx)
    · exfalso
      -- a point above the curve strictly below the crossing forces a
      -- second crossing below x via the orientation machinery
      have hstrict := crossing_threshold_strict ν hν hc1 hc2 hx heq
      have h2 := (crossing_orientation_below ν hν hc1 hc2 hy)
      by_cases hb : (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + y ^ 2) < ν + c
      · linarith [h2 hb, h]
      · push_neg at hb
        -- y is at/above the threshold; the after-orientation at y...
        -- use existence of the crossing scale window: there is a
        -- crossing z; uniqueness forces z = x; then y with ρ > B and
        -- y < x contradicts orientation after applied at... direct:
        -- IVT between y and x: D y > 0, D x = 0... take the W-argument:
        -- crossing_orientation_after at the crossing y? y is NOT a
        -- crossing.  Use: D y > 0 and D x = 0 with y < x: the set of
        -- crossings in [y, x] has an infimum which is a crossing with
        -- left-positive approach — slope ≤ 0 there — but its threshold
        -- is ≥ y's ≥ threshold strict?  hb gives y at/above threshold:
        -- every point in (y, x] is STRICTLY above (sqrt strictly
        -- increasing), so the first crossing w in (y, x] has strict
        -- threshold and slope ≤ 0 — contradiction with D′(w) > 0.
        have hDy : 0 < besselIReal (ν + 1) y / besselIReal ν y
            - amosFamily ν c y := by linarith [h]
        -- first crossing in [y, x]
        set D : ℝ → ℝ := fun z =>
          besselIReal (ν + 1) z / besselIReal ν z - amosFamily ν c z
          with hD_def
        have hDx0 : D x = 0 := by simp only [hD_def]; linarith [heq]
        have hcont : ContinuousOn D (Set.Icc y x) := by
          intro z hz
          have hz0 : 0 < z := lt_of_lt_of_le hy hz.1
          exact ((crossing_hasDerivAt_everywhere ν hν c hz0).continuousAt).continuousWithinAt
        set W := {z : ℝ | z ∈ Set.Icc y x ∧ D z ≤ 0} with hW_def
        have hWne : W.Nonempty := ⟨x, ⟨le_of_lt hyx, le_refl _⟩, le_of_eq hDx0⟩
        have hWbdd : BddBelow W := ⟨y, fun z hz => hz.1.1⟩
        have hWclosed : IsClosed W := by
          have : W = Set.Icc y x ∩ D ⁻¹' (Set.Iic 0) := by
            ext z
            simp [hW_def, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
          rw [this]
          exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
        set w := sInf W with hw_def
        have hwmem : w ∈ W := hWclosed.csInf_mem hWne hWbdd
        have hwy : y ≤ w := le_csInf hWne (fun z hz => hz.1.1)
        have hw0 : 0 < w := lt_of_lt_of_le hy hwy
        have hwney : w ≠ y := by
          intro hh
          rw [hh] at hwmem
          have h2 := hwmem.2
          simp only [hD_def] at h2
          linarith [h2, hDy]
        have hwy' : y < w := lt_of_le_of_ne hwy (Ne.symm hwney)
        have hleftpos : ∀ z, y < z → z < w → 0 < D z := by
          intro z h1 h2
          by_contra hzc
          push_neg at hzc
          have hzmem : z ∈ W := by
            refine ⟨⟨le_of_lt h1, ?_⟩, hzc⟩
            exact le_of_lt (lt_of_lt_of_le h2 hwmem.1.2)
          exact absurd (csInf_le hWbdd hzmem) (not_le.mpr h2)
        have htendsto : Tendsto D (𝓝[<] w) (𝓝 (D w)) :=
          ((crossing_hasDerivAt_everywhere ν hν c hw0).continuousAt).continuousWithinAt
        have hev_ge : ∀ᶠ z in 𝓝[<] w, 0 ≤ D z := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hwy')] with z hz1 hz2
          exact le_of_lt (hleftpos z hz2 hz1)
        have hDw : D w = 0 :=
          le_antisymm hwmem.2 (ge_of_tendsto htendsto hev_ge)
        have heqw : besselIReal (ν + 1) w / besselIReal ν w
            = amosFamily ν c w := by
          simp only [hD_def] at hDw
          linarith [hDw]
        -- slope at w from the left is ≤ 0
        have hDw' := crossing_hasDerivAt ν hν hw0 heqw
        have hslope := (hasDerivAt_iff_tendsto_slope.mp hDw').mono_left
          (nhdsWithin_mono w (fun z (hz : z ∈ Set.Iio w) => ne_of_lt hz))
        have hev_slope : ∀ᶠ z in 𝓝[<] w, slope D w z ≤ 0 := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hwy')] with z hz1 hz2
          rw [slope_def_field]
          have hDz := hleftpos z hz2 hz1
          have hzw : z - w < 0 := sub_neg.mpr hz1
          apply le_of_lt
          apply div_neg_of_pos_of_neg
          · simp only [hD_def] at hDz ⊢
            linarith [hDw, hDz]
          · exact hzw
        have hV_le : amosFamily ν c w / w
            * (2 * c - 1 - (ν + c) / Real.sqrt ((ν + c) ^ 2 + w ^ 2)) ≤ 0 :=
          le_of_tendsto hslope hev_slope
        -- but w has the STRICT threshold (w > y ≥ threshold point)
        have hsw : Real.sqrt ((ν + c) ^ 2 + y ^ 2)
            < Real.sqrt ((ν + c) ^ 2 + w ^ 2) := by
          apply Real.sqrt_lt_sqrt (by positivity)
          nlinarith [hwy', hy]
        have hswpos : 0 < Real.sqrt ((ν + c) ^ 2 + w ^ 2) :=
          Real.sqrt_pos.mpr (by positivity)
        have hfacpos : 0 < 2 * c - 1
            - (ν + c) / Real.sqrt ((ν + c) ^ 2 + w ^ 2) := by
          rw [sub_pos, div_lt_iff₀ hswpos]
          calc ν + c ≤ (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + y ^ 2) := hb
            _ < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + w ^ 2) :=
                mul_lt_mul_of_pos_left hsw (by linarith)
        nlinarith [hV_le, hfacpos,
          div_pos (amosFamily_pos ν c hw0) hw0]
  · intro hxy
    exact crossing_orientation_after ν hν hc1 hc2 hx heq
      (crossing_threshold_strict ν hν hc1 hc2 hx heq) hxy

end AmosClosure
