/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.AmosLowerReal

/-!
# The crossing phase, block A: the ψ sandwich and the lower half of
the family classification (arc C5, phase 3; charter Amendment 3)

`2ν+1 < ψ_ν(x) < 2ν+2` globally: the lower half is C4's barrier
theorem; the upper half is a new machine-checked ENDPOINT of the
formal development but CLASSICAL mathematics (charter Amendment 4):
by the ratio recurrence it is equivalent to `ρ_ν > ρ_{ν+1}`, i.e.
to the TURAN INEQUALITY `I_{ν+1}² > I_ν·I_{ν+2}` at `μ = ν+1`
(Baricz arXiv:1010.3346; Gronwall, Thiruvenkatachar–Nanjundiah,
Amos).  Route here: `L_ν > B_{ν,1}` everywhere (the root sum
strictly exceeds `a+b`), so `ρ_ν > B_{ν,1}`, which by the general
calibration is exactly `ψ_ν < 2ν+2`; the Turán form is derived as
the named endpoint `besselIReal_turan`.  Corollary, killing every
`c ≥ 1`: `B_{ν,c}` is a uniform LOWER bound (RS16's `α ≥ 1` half).
Blocks B–E (existence, threshold, uniqueness, scale) follow in
later commits per the registered plan.
-/

open Set Filter Topology

namespace AmosClosure

/-- `B_{ν,1} < L_ν` everywhere: the root difference is `< 1/2`
because the root sum strictly exceeds `a + b = 2ν + 5/2`. -/
lemma amosFamily_one_lt_amosLower (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    amosFamily ν 1 x < amosLower ν x := by
  unfold amosFamily amosLower
  set sa := Real.sqrt ((ν + 1) ^ 2 + x ^ 2) with hsa_def
  set sb := Real.sqrt ((ν + 3 / 2) ^ 2 + x ^ 2) with hsb_def
  have hsa2 : sa ^ 2 = (ν + 1) ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hsb2 : sb ^ 2 = (ν + 3 / 2) ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hsa0 : 0 ≤ sa := Real.sqrt_nonneg _
  have hsb0 : 0 ≤ sb := Real.sqrt_nonneg _
  have hsa_gt : ν + 1 < sa := by nlinarith [hsa2, hsa0, hx]
  have hsb_gt : ν + 3 / 2 < sb := by nlinarith [hsb2, hsb0, hx]
  -- root difference: (sb − sa)(sb + sa) = (ν+5/4) · 1 ... = b² − a²
  have hprod : (sb - sa) * (sb + sa)
      = (ν + 3 / 2) ^ 2 - (ν + 1) ^ 2 := by nlinarith [hsa2, hsb2]
  have hsum : 2 * ν + 5 / 2 < sa + sb := by linarith
  have hdiff : sb - sa < 1 / 2 := by
    nlinarith [hprod, hsum, hsa0, hsb0]
  have hdL : (0 : ℝ) < ν + 1 / 2 + sb := by linarith
  have hdB : (0 : ℝ) < ν + 1 + sa := by linarith
  rw [div_lt_div_iff₀ hdB hdL]
  nlinarith [hdiff, hx]

/-- **The ψ upper sandwich** (block A headline; a new
machine-checked endpoint of this development — mathematically the
CLASSICAL Turán inequality in disguise, see `besselIReal_turan`):
`ψ_ν(x) < 2ν+2` for every real `ν ≥ 0`, `x > 0` — together with
C4's `besselPsiReal_gt`, the barrier variable lives strictly
between its two calibration levels. -/
theorem besselPsiReal_lt (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    besselPsiReal ν x < 2 * ν + 2 := by
  have hB1 : amosFamily ν 1 x < besselRatioReal ν x :=
    lt_trans (amosFamily_one_lt_amosLower ν hν hx)
      (besselLowerReal_holds ν hν hx)
  have hcal := amosFamily_calibration ν 1 hx
  have hρ := besselRatioReal_pos hν hx
  have hB1pos := amosFamily_pos ν 1 hx
  have hρ' : besselRatioReal ν x ≠ 0 := ne_of_gt hρ
  have hB1' : amosFamily ν 1 x ≠ 0 := ne_of_gt hB1pos
  -- reversed antitone conversion: ρ > B₁ ⟹ 1/ρ − ρ < 1/B₁ − B₁
  have hexp : (1 / amosFamily ν 1 x - amosFamily ν 1 x
      - (1 / besselRatioReal ν x - besselRatioReal ν x))
      * (amosFamily ν 1 x * besselRatioReal ν x)
      = (besselRatioReal ν x - amosFamily ν 1 x)
        * (1 + amosFamily ν 1 x * besselRatioReal ν x) := by
    field_simp
    ring
  have hmul : 0 < amosFamily ν 1 x * besselRatioReal ν x :=
    mul_pos hB1pos hρ
  have hprodpos : 0 < (besselRatioReal ν x - amosFamily ν 1 x)
      * (1 + amosFamily ν 1 x * besselRatioReal ν x) :=
    mul_pos (by linarith [hB1]) (by linarith [hmul])
  have hsdiff : 0 < 1 / amosFamily ν 1 x - amosFamily ν 1 x
      - (1 / besselRatioReal ν x - besselRatioReal ν x) := by
    have h2 := hprodpos
    rw [← hexp] at h2
    rcases mul_pos_iff.mp h2 with ⟨hA, _⟩ | ⟨_, hM⟩
    · exact hA
    · linarith [hmul, hM]
  have hlt : 1 / besselRatioReal ν x - besselRatioReal ν x
      < 2 * (ν + 1) / x := by
    linarith [hsdiff, hcal]
  have hψ : besselPsiReal ν x
      = x * (1 / besselRatioReal ν x - besselRatioReal ν x) := rfl
  rw [hψ]
  calc x * (1 / besselRatioReal ν x - besselRatioReal ν x)
      < x * (2 * (ν + 1) / x) := by
        exact mul_lt_mul_of_pos_left hlt hx
    _ = 2 * ν + 2 := by
        rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hx)]
        ring

/-- **The lower half of the family classification** (RS16's
`α ≥ 1` half, free from block A): every `c ≥ 1` gives a uniform
LOWER bound at every real order. -/
theorem amosFamily_lower_of_one_le (ν : ℝ) (hν : 0 ≤ ν) {c : ℝ}
    (hc : 1 ≤ c) {x : ℝ} (hx : 0 < x) :
    amosFamily ν c x < besselIReal (ν + 1) x / besselIReal ν x :=
  calc amosFamily ν c x
      ≤ amosFamily ν 1 x := amosFamily_anti ν hx hc
    _ < amosLower ν x := amosFamily_one_lt_amosLower ν hν hx
    _ < besselIReal (ν + 1) x / besselIReal ν x :=
        besselLowerReal_holds ν hν hx

/-! ### Block B: existence of the crossing for every `(ν, c)`,
`1/2 < c < 1` (charter Amendments 2–3: witnesses `x₋(c) = √(1−c)`
and `x₊(ν,c) = 2D̂/(2c−1)`, then the intermediate value theorem). -/

/-- Product-form upper bound on the ratio (C4's zone toolkit,
repackaged): `ρ_ν(x) < x/(2(ν+1)(1−q))` with `q = (x/2)²/(ν+2)`,
for `q < 1`. -/
lemma besselRatioReal_lt_product (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) (hq : (x / 2) ^ 2 / (ν + 2) < 1) :
    besselIReal (ν + 1) x / besselIReal ν x
      < x / (2 * (ν + 1) * (1 - (x / 2) ^ 2 / (ν + 2))) := by
  have hq0 : (0 : ℝ) ≤ (x / 2) ^ 2 / (ν + 2) :=
    div_nonneg (by positivity) (by linarith)
  have h1q : (0 : ℝ) < 1 - (x / 2) ^ 2 / (ν + 2) := by linarith
  have hI1 := besselIReal_pos (ν + 1) (by linarith) hx
  have ht0 := besselRealTerm_pos ν hν 0 hx
  have ht10 := besselRealTerm_pos (ν + 1) (by linarith) 0 hx
  have hlo := besselRealTerm_zero_lt_besselIReal ν hν hx
  have hid := besselRealTerm_zero_succ ν hν hx
  -- (1−q)·I_{ν+1} ≤ t_{ν+1,0}, with the (ν+1)+1 = ν+2 shape rewrite
  have hup : (1 - (x / 2) ^ 2 / (ν + 2)) * besselIReal (ν + 1) x
      ≤ besselRealTerm (ν + 1) 0 x := by
    have h := besselIReal_mul_le (ν + 1) (by linarith) hx
      (by rw [show ν + 1 + 1 = ν + 2 by ring]; exact hq)
    rwa [show ν + 1 + 1 = ν + 2 by ring] at h
  -- chain: ρ < I_{ν+1}/t_{ν,0} ≤ [t_{ν+1,0}/(1−q)]/t_{ν,0} = RHS
  have hstep1 : besselIReal (ν + 1) x / besselIReal ν x
      < besselIReal (ν + 1) x / besselRealTerm ν 0 x := by
    rw [div_lt_div_iff₀ (besselIReal_pos ν hν hx) ht0]
    exact mul_lt_mul_of_pos_left hlo hI1
  have hstep2 : besselIReal (ν + 1) x / besselRealTerm ν 0 x
      ≤ x / (2 * (ν + 1) * (1 - (x / 2) ^ 2 / (ν + 2))) := by
    rw [div_le_div_iff₀ ht0 (by positivity)]
    -- I_{ν+1} · 2(ν+1)(1−q) ≤ x · t_{ν,0} = 2(ν+1)·t_{ν+1,0}
    have h := mul_le_mul_of_nonneg_left hup
      (by linarith : (0 : ℝ) ≤ 2 * (ν + 1))
    nlinarith [h, hid, ht0]
  linarith [hstep1, hstep2]

/-- Small-side witness, generalized (charter Amendments 2–3): at
EVERY `0 < x ≤ √(1−c)`, uniformly in `ν ≥ 0`, the ratio is strictly
below `B_{ν,c}` — the negative anchor for all first-crossing
arguments. -/
lemma crossing_witness_small_le (ν : ℝ) (hν : 0 ≤ ν) {c x : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) (hx : 0 < x)
    (hxle : x ≤ Real.sqrt (1 - c)) :
    besselIReal (ν + 1) x / besselIReal ν x < amosFamily ν c x := by
  have hx2 : x ^ 2 ≤ 1 - c := by
    have h := pow_le_pow_left₀ hx.le hxle 2
    rwa [Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - c)] at h
  have hq : (x / 2) ^ 2 / (ν + 2) < 1 := by
    rw [div_lt_one (by linarith)]
    nlinarith [hx2]
  have hprod := besselRatioReal_lt_product ν hν hx hq
  -- B_{ν,c}(x₋) dominates the product bound: denominators reversed
  have hsa : Real.sqrt ((ν + c) ^ 2 + x ^ 2)
      ≤ (ν + c) + x ^ 2 / (2 * (ν + c)) := by
    have ha : (0 : ℝ) < ν + c := by linarith
    have hrhs : (0 : ℝ) ≤ (ν + c) + x ^ 2 / (2 * (ν + c)) := by positivity
    rw [show (ν + c) ^ 2 + x ^ 2
        = ((ν + c) + x ^ 2 / (2 * (ν + c))) ^ 2
          - (x ^ 2 / (2 * (ν + c))) ^ 2 by field_simp; ring]
    calc Real.sqrt (((ν + c) + x ^ 2 / (2 * (ν + c))) ^ 2
          - (x ^ 2 / (2 * (ν + c))) ^ 2)
        ≤ Real.sqrt (((ν + c) + x ^ 2 / (2 * (ν + c))) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg (x ^ 2 / (2 * (ν + c)))]
      _ = (ν + c) + x ^ 2 / (2 * (ν + c)) := Real.sqrt_sq hrhs
  have hkey : (ν + c) + Real.sqrt ((ν + c) ^ 2 + x ^ 2)
      < 2 * (ν + 1) * (1 - (x / 2) ^ 2 / (ν + 2)) := by
    have ha : (0 : ℝ) < ν + c := by linarith
    have h1 : x ^ 2 / (2 * (ν + c)) < x ^ 2 := by
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (ν + c))]
      nlinarith [mul_pos hx hx, hc1, hν]
    -- the registered arithmetic: (x²/2)(1/(ν+c) + (ν+1)/(ν+2)) < 2(1−c)
    have harith : x ^ 2 / (2 * (ν + c))
        + 2 * (ν + 1) * ((x / 2) ^ 2 / (ν + 2)) < 2 * (1 - c) := by
      have hxc : x ^ 2 ≤ 1 - c := hx2
      have hf1 : x ^ 2 / (2 * (ν + c)) < x ^ 2 := h1
      have hf2 : 2 * (ν + 1) * ((x / 2) ^ 2 / (ν + 2)) ≤ x ^ 2 / 2 := by
        have hr := real_zone_ratio_uniform ν hν
        have hmono := mul_le_mul_of_nonneg_left hr
          (by positivity : (0 : ℝ) ≤ x ^ 2 / 2)
        have hEq : 2 * (ν + 1) * ((x / 2) ^ 2 / (ν + 2))
            = x ^ 2 / 2 * ((ν + 1) / (ν + 2)) := by
          field_simp
        rw [hEq]
        linarith [hmono]
      nlinarith [hf1, hf2, hxc, hc1]
    nlinarith [hsa, harith, hx2]
  unfold amosFamily
  have hdB : (0 : ℝ) < ν + c + Real.sqrt ((ν + c) ^ 2 + x ^ 2) := by
    have := amosFamily_denom_pos ν c hx
    exact this
  calc besselIReal (ν + 1) x / besselIReal ν x
      < x / (2 * (ν + 1) * (1 - (x / 2) ^ 2 / (ν + 2))) := hprod
    _ ≤ x / (ν + c + Real.sqrt ((ν + c) ^ 2 + x ^ 2)) := by
        rw [div_le_div_iff₀ (by nlinarith [hkey, hdB]) hdB]
        nlinarith [hkey, hx]

/-- Large-side witness (charter Amendment 2): at
`x₊ = 2D̂/(2c−1)`, `D̂ = (ν+3/2)² − (ν+c)²`, the ratio is strictly
above `B_{ν,c}` (through the lower barrier `L`). -/
lemma crossing_witness_large (ν : ℝ) (hν : 0 ≤ ν) {c : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) :
    amosFamily ν c (2 * ((ν + 3 / 2) ^ 2 - (ν + c) ^ 2) / (2 * c - 1))
      < besselIReal (ν + 1) (2 * ((ν + 3 / 2) ^ 2 - (ν + c) ^ 2) / (2 * c - 1))
        / besselIReal ν (2 * ((ν + 3 / 2) ^ 2 - (ν + c) ^ 2) / (2 * c - 1)) := by
  have h2c : (0 : ℝ) < 2 * c - 1 := by linarith
  have hD : (0 : ℝ) < (ν + 3 / 2) ^ 2 - (ν + c) ^ 2 := by nlinarith
  set X := 2 * ((ν + 3 / 2) ^ 2 - (ν + c) ^ 2) / (2 * c - 1) with hX_def
  have hX : 0 < X := by rw [hX_def]; positivity
  -- B_{ν,c}(X) < L_ν(X): root difference < c − 1/2 at X
  have hBL : amosFamily ν c X < amosLower ν X := by
    unfold amosFamily amosLower
    set sa := Real.sqrt ((ν + c) ^ 2 + X ^ 2) with hsa_def
    set sb := Real.sqrt ((ν + 3 / 2) ^ 2 + X ^ 2) with hsb_def
    have hsa2 : sa ^ 2 = (ν + c) ^ 2 + X ^ 2 := Real.sq_sqrt (by positivity)
    have hsb2 : sb ^ 2 = (ν + 3 / 2) ^ 2 + X ^ 2 := Real.sq_sqrt (by positivity)
    have hsa0 : 0 ≤ sa := Real.sqrt_nonneg _
    have hsb0 : 0 ≤ sb := Real.sqrt_nonneg _
    have hsaX : X < sa := by nlinarith [hsa2, hsa0, hX, hc1, hν]
    have hsbX : X < sb := by nlinarith [hsb2, hsb0, hX]
    have hprod : (sb - sa) * (sb + sa)
        = (ν + 3 / 2) ^ 2 - (ν + c) ^ 2 := by nlinarith [hsa2, hsb2]
    have hXval : (2 * c - 1) * X = 2 * ((ν + 3 / 2) ^ 2 - (ν + c) ^ 2) := by
      rw [hX_def]
      field_simp
    have hdiff : sb - sa < c - 1 / 2 := by
      nlinarith [hprod, hXval, hsaX, hsbX, h2c,
        mul_lt_mul_of_pos_left (by linarith [hsaX, hsbX] : 2 * X < sa + sb)
          (by linarith : (0:ℝ) < c - 1/2)]
    have hdL : (0 : ℝ) < ν + 1 / 2 + sb := by linarith
    have hdB : (0 : ℝ) < ν + c + sa := by linarith [hsaX, hX]
    rw [div_lt_div_iff₀ hdB hdL]
    nlinarith [hdiff, hX]
  calc amosFamily ν c X < amosLower ν X := hBL
    _ < besselIReal (ν + 1) X / besselIReal ν X :=
        besselLowerReal_holds ν hν hX

/-- **EXISTENCE OF THE CROSSING** (block B endpoint): for every
`ν ≥ 0` and `1/2 < c < 1` there is an `x_* > 0` with
`ρ_ν(x_*) = B_{ν,c}(x_*)`, located in the explicit window
`[√(1−c), 2D̂/(2c−1)]`. -/
theorem amosFamily_crossing_exists (ν : ℝ) (hν : 0 ≤ ν) {c : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) :
    ∃ x : ℝ, Real.sqrt (1 - c) ≤ x
      ∧ x ≤ 2 * ((ν + 3 / 2) ^ 2 - (ν + c) ^ 2) / (2 * c - 1)
      ∧ besselIReal (ν + 1) x / besselIReal ν x = amosFamily ν c x := by
  have h2c : (0 : ℝ) < 2 * c - 1 := by linarith
  have hD : (0 : ℝ) < (ν + 3 / 2) ^ 2 - (ν + c) ^ 2 := by nlinarith
  set xm := Real.sqrt (1 - c) with hxm_def
  set X := 2 * ((ν + 3 / 2) ^ 2 - (ν + c) ^ 2) / (2 * c - 1) with hX_def
  have hxm : 0 < xm := Real.sqrt_pos.mpr (by linarith)
  have hxm1 : xm ≤ 1 := by
    rw [hxm_def]
    calc Real.sqrt (1 - c) ≤ Real.sqrt 1 :=
          Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have hX2 : 2 < X := by
    rw [hX_def]
    rw [lt_div_iff₀ h2c]
    nlinarith
  have hle : xm ≤ X := by linarith
  -- the difference function, continuous on the window
  set D : ℝ → ℝ := fun y =>
    besselIReal (ν + 1) y / besselIReal ν y - amosFamily ν c y with hD_def
  have hcont : ContinuousOn D (Set.Icc xm X) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hxm hy.1
    have h1 : ContinuousAt (fun z => besselIReal (ν + 1) z / besselIReal ν z) y :=
      (besselRatioReal_hasDerivAt ν hν hy0).continuousAt
    have h2 : ContinuousAt (fun z => amosFamily ν c z) y := by
      have hden : ContinuousAt
          (fun z : ℝ => ν + c + Real.sqrt ((ν + c) ^ 2 + z ^ 2)) y := by
        fun_prop
      have hne : ν + c + Real.sqrt ((ν + c) ^ 2 + y ^ 2) ≠ 0 :=
        ne_of_gt (amosFamily_denom_pos ν c hy0)
      exact (continuousAt_id.div hden hne)
    exact (h1.sub h2).continuousWithinAt
  have hDm : D xm < 0 := by
    have h := crossing_witness_small_le ν hν hc1 hc2 hxm
      (by rw [hxm_def])
    simp only [hD_def]
    linarith [h]
  have hDX : 0 < D X := by
    have h := crossing_witness_large ν hν hc1 hc2
    rw [← hX_def] at h
    simp only [hD_def]
    linarith [h]
  have h0mem : (0 : ℝ) ∈ Set.Icc (D xm) (D X) := ⟨le_of_lt hDm, le_of_lt hDX⟩
  obtain ⟨x, hxmem, hDx⟩ := intermediate_value_Icc hle hcont h0mem
  refine ⟨x, hxmem.1, hxmem.2, ?_⟩
  have : D x = 0 := hDx
  simp only [hD_def] at this
  linarith [this]

/-- **The Turán inequality at real order** (block A′, charter
Amendment 4; classical — Baricz arXiv:1010.3346 and antecedents —
machine-checked here as the registered equivalent of the ψ upper
sandwich): `I_ν(x)·I_{ν+2}(x) < I_{ν+1}(x)²`. -/
theorem besselIReal_turan (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    besselIReal ν x * besselIReal (ν + 2) x
      < besselIReal (ν + 1) x ^ 2 := by
  have hψ := besselPsiReal_lt ν hν hx
  have hrec := besselIReal_ratio_recurrence ν hν hx
  have h0 := besselIReal_pos ν hν hx
  have h1 := besselIReal_pos (ν + 1) (by linarith) hx
  have hψdef : besselPsiReal ν x
      = x * (1 / (besselIReal (ν + 1) x / besselIReal ν x)
        - besselIReal (ν + 1) x / besselIReal ν x) := rfl
  rw [hψdef, hrec] at hψ
  -- ρ_{ν+1} < ρ_ν from x(ρ_{ν+1} − ρ_ν) + 2ν+2 < 2ν+2
  have hlt : besselIReal (ν + 2) x / besselIReal (ν + 1) x
      < besselIReal (ν + 1) x / besselIReal ν x := by
    by_contra hcon
    push_neg at hcon
    have hxt : x * (2 * (ν + 1) / x) = 2 * (ν + 1) := by
      field_simp
    have hmul := mul_le_mul_of_nonneg_left hcon hx.le
    nlinarith [hψ, hxt, hmul]
  rw [div_lt_div_iff₀ h1 h0] at hlt
  nlinarith [hlt]

/-! ### Blocks C–D–E: threshold, uniqueness, orientation, scale
(charter Amendment 3).  The possible degenerate touch EXACTLY at
the threshold is the registered named caveat: uniqueness and
orientation are stated for strict-threshold crossings. -/

/-- Derivative of the family member in `x`:
`B_{ν,c}'(x) = a/(s·(a+s))` with `a = ν+c`, `s = √(a²+x²)`. -/
lemma amosFamily_hasDerivAt (ν c : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => amosFamily ν c y)
      ((ν + c) / (Real.sqrt ((ν + c) ^ 2 + x ^ 2)
        * (ν + c + Real.sqrt ((ν + c) ^ 2 + x ^ 2)))) x := by
  have hu : (0 : ℝ) < (ν + c) ^ 2 + x ^ 2 := by positivity
  have hden : 0 < ν + c + Real.sqrt ((ν + c) ^ 2 + x ^ 2) :=
    amosFamily_denom_pos ν c hx
  have hspos : 0 < Real.sqrt ((ν + c) ^ 2 + x ^ 2) :=
    Real.sqrt_pos.mpr hu
  have hs2 : Real.sqrt ((ν + c) ^ 2 + x ^ 2) ^ 2 = (ν + c) ^ 2 + x ^ 2 :=
    Real.sq_sqrt hu.le
  have hinner : HasDerivAt (fun y : ℝ => (ν + c) ^ 2 + y ^ 2) (2 * x) x := by
    have h := (hasDerivAt_pow 2 x).const_add ((ν + c) ^ 2)
    simpa using h
  have hsqrt : HasDerivAt (fun y => Real.sqrt ((ν + c) ^ 2 + y ^ 2))
      (2 * x / (2 * Real.sqrt ((ν + c) ^ 2 + x ^ 2))) x :=
    hinner.sqrt (ne_of_gt hu)
  have hdenom : HasDerivAt
      (fun y => ν + c + Real.sqrt ((ν + c) ^ 2 + y ^ 2))
      (2 * x / (2 * Real.sqrt ((ν + c) ^ 2 + x ^ 2))) x := by
    simpa using hsqrt.const_add (ν + c)
  have hdiv := (hasDerivAt_id x).div hdenom (ne_of_gt hden)
  have hfun : (fun y => amosFamily ν c y)
      = fun y => y / (ν + c + Real.sqrt ((ν + c) ^ 2 + y ^ 2)) := rfl
  rw [hfun]
  convert hdiv using 1
  set s := Real.sqrt ((ν + c) ^ 2 + x ^ 2) with hs_def
  have hnum : ν + c + s - x * (2 * x / (2 * s)) = (ν + c) * (ν + c + s) / s := by
    have h2 : x * (2 * x / (2 * s)) = x ^ 2 / s := by
      field_simp
    rw [h2]
    field_simp
    linear_combination hs2
  simp only [id_eq]
  rw [show (1 : ℝ) * (ν + c + s) - x * (2 * x / (2 * s))
      = ν + c + s - x * (2 * x / (2 * s)) by ring, hnum]
  have hs' : s ≠ 0 := ne_of_gt hspos
  have hd' : (ν + c + s) ≠ 0 := ne_of_gt hden
  field_simp

/-- The crossing-slope identity: at any equality point, the
difference `D = ρ − B_c` has derivative
`(B_c/x)·(2c−1 − a/s)`. -/
lemma crossing_hasDerivAt (ν : ℝ) (hν : 0 ≤ ν) {c x : ℝ}
    (hx : 0 < x)
    (heq : besselIReal (ν + 1) x / besselIReal ν x = amosFamily ν c x) :
    HasDerivAt (fun y => besselIReal (ν + 1) y / besselIReal ν y
        - amosFamily ν c y)
      (amosFamily ν c x / x
        * (2 * c - 1 - (ν + c) / Real.sqrt ((ν + c) ^ 2 + x ^ 2))) x := by
  have hρ' := besselRatioReal_hasDerivAt ν hν hx
  have hB' := amosFamily_hasDerivAt ν c hx
  have hsub := hρ'.sub hB'
  convert hsub using 1
  have hQ : riccatiQReal ν x (besselIReal (ν + 1) x / besselIReal ν x)
      = (2 * c - 1) / x * amosFamily ν c x := by
    rw [heq]
    exact riccatiQReal_amosFamily ν c hx
  rw [show riccatiQReal ν x (besselRatioReal ν x)
      = riccatiQReal ν x (besselIReal (ν + 1) x / besselIReal ν x) from rfl,
    hQ]
  unfold amosFamily
  set s := Real.sqrt ((ν + c) ^ 2 + x ^ 2) with hs_def
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hden : 0 < ν + c + s := by
    have := amosFamily_denom_pos ν c hx
    rwa [← hs_def] at this
  field_simp

/-- **BLOCK C — no crossing below the threshold**: every equality
point satisfies `ν+c ≤ (2c−1)·s(x)` (equivalently `x ≥ x_†`). -/
theorem crossing_threshold (ν : ℝ) (hν : 0 ≤ ν) {c x : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) (hx : 0 < x)
    (heq : besselIReal (ν + 1) x / besselIReal ν x = amosFamily ν c x) :
    ν + c ≤ (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + x ^ 2) := by
  by_contra hcon
  push_neg at hcon
  -- anchor strictly below x with a negative value
  set a₀ : ℝ := min (Real.sqrt (1 - c)) (x / 2) with ha0_def
  have hsq : 0 < Real.sqrt (1 - c) := Real.sqrt_pos.mpr (by linarith)
  have ha0 : 0 < a₀ := lt_min hsq (by linarith)
  have ha0x : a₀ < x := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set D : ℝ → ℝ := fun y =>
    besselIReal (ν + 1) y / besselIReal ν y - amosFamily ν c y with hD_def
  have hDa0 : D a₀ < 0 := by
    have h := crossing_witness_small_le ν hν hc1 hc2 ha0 (min_le_left _ _)
    simp only [hD_def]
    linarith [h]
  have hDx : D x = 0 := by simp only [hD_def]; linarith [heq]
  have hcont : ContinuousOn D (Set.Icc a₀ x) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha0 hy.1
    exact (((besselRatioReal_hasDerivAt ν hν hy0).sub
      (amosFamily_hasDerivAt ν c hy0)).continuousAt).continuousWithinAt
  -- first nonnegative point
  set S := {y : ℝ | y ∈ Set.Icc a₀ x ∧ 0 ≤ D y} with hS_def
  have hSne : S.Nonempty := ⟨x, ⟨le_of_lt ha0x, le_refl x⟩, le_of_eq hDx.symm⟩
  have hSbdd : BddBelow S := ⟨a₀, fun y hy => hy.1.1⟩
  have hSclosed : IsClosed S := by
    have : S = Set.Icc a₀ x ∩ D ⁻¹' (Set.Ici 0) := by
      ext y
      simp [hS_def, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    rw [this]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  set z := sInf S with hz_def
  have hzmem : z ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hza0 : a₀ ≤ z := le_csInf hSne (fun y hy => hy.1.1)
  have hz0 : 0 < z := lt_of_lt_of_le ha0 hza0
  have hzne : z ≠ a₀ := by
    intro h
    rw [h] at hzmem
    linarith [hzmem.2, hDa0]
  have hza0' : a₀ < z := lt_of_le_of_ne hza0 (Ne.symm hzne)
  have hleft : ∀ y, a₀ < y → y < z → D y < 0 := by
    intro y h1 h2
    by_contra hy
    push_neg at hy
    have hymem : y ∈ S := by
      refine ⟨⟨le_of_lt h1, ?_⟩, hy⟩
      exact le_of_lt (lt_of_lt_of_le h2 hzmem.1.2)
    exact absurd (csInf_le hSbdd hymem) (not_le.mpr h2)
  -- D z = 0 by left continuity
  have htendsto : Tendsto D (𝓝[<] z) (𝓝 (D z)) :=
    (((besselRatioReal_hasDerivAt ν hν hz0).sub
      (amosFamily_hasDerivAt ν c hz0)).continuousAt).continuousWithinAt
  have hev_le : ∀ᶠ y in 𝓝[<] z, D y ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hza0')] with y hy1 hy2
    exact le_of_lt (hleft y hy2 hy1)
  have hDz_le : D z ≤ 0 := le_of_tendsto htendsto hev_le
  have hDz : D z = 0 := le_antisymm hDz_le hzmem.2
  -- z is a crossing: slope from the left is ≥ 0
  have heqz : besselIReal (ν + 1) z / besselIReal ν z = amosFamily ν c z := by
    simp only [hD_def] at hDz
    linarith [hDz]
  have hDz' := crossing_hasDerivAt ν hν hz0 heqz
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hDz').mono_left
    (nhdsWithin_mono z (fun y (hy : y ∈ Set.Iio z) => ne_of_lt hy))
  have hev_slope : ∀ᶠ y in 𝓝[<] z, 0 ≤ slope D z y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hza0')] with y hy1 hy2
    rw [slope_def_field]
    have hDy := hleft y hy2 hy1
    have hyz : y - z < 0 := sub_neg.mpr hy1
    apply le_of_lt
    apply div_pos_iff.mpr
    exact Or.inr ⟨by simp only [hD_def] at hDy ⊢; linarith [hDz, hDy], hyz⟩
  have hV_ge : 0 ≤ amosFamily ν c z / z
      * (2 * c - 1 - (ν + c) / Real.sqrt ((ν + c) ^ 2 + z ^ 2)) :=
    ge_of_tendsto hslope hev_slope
  -- but the threshold is violated at z ≤ x: slope must be negative
  have hsz : Real.sqrt ((ν + c) ^ 2 + z ^ 2)
      ≤ Real.sqrt ((ν + c) ^ 2 + x ^ 2) := by
    apply Real.sqrt_le_sqrt
    have hzx : z ≤ x := hzmem.1.2
    nlinarith [hzx, hz0]
  have hszpos : 0 < Real.sqrt ((ν + c) ^ 2 + z ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hfac : 2 * c - 1 - (ν + c) / Real.sqrt ((ν + c) ^ 2 + z ^ 2) < 0 := by
    rw [sub_neg, lt_div_iff₀ hszpos]
    calc (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + z ^ 2)
        ≤ (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + x ^ 2) :=
          mul_le_mul_of_nonneg_left hsz (by linarith)
      _ < ν + c := hcon
  have hBz := amosFamily_pos ν c hz0
  nlinarith [hV_ge, hfac, div_pos hBz hz0]

/-- Right-of-crossing positivity for STRICT-threshold crossings:
just to the right (up to any `b > x₁`) there is a point where the
difference is positive; and below-left, negative (used by D/E). -/
lemma crossing_pos_right (ν : ℝ) (hν : 0 ≤ ν) {c x₁ b : ℝ}
    (hc1 : 1 / 2 < c) (hx₁ : 0 < x₁) (hb : x₁ < b)
    (heq : besselIReal (ν + 1) x₁ / besselIReal ν x₁ = amosFamily ν c x₁)
    (hstrict : ν + c < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + x₁ ^ 2)) :
    ∃ m, x₁ < m ∧ m < b
      ∧ 0 < besselIReal (ν + 1) m / besselIReal ν m - amosFamily ν c m := by
  set D : ℝ → ℝ := fun y =>
    besselIReal (ν + 1) y / besselIReal ν y - amosFamily ν c y with hD_def
  have hD₁ : D x₁ = 0 := by simp only [hD_def]; linarith [heq]
  have hDz' := crossing_hasDerivAt ν hν hx₁ heq
  have hszpos : 0 < Real.sqrt ((ν + c) ^ 2 + x₁ ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hV_pos : 0 < amosFamily ν c x₁ / x₁
      * (2 * c - 1 - (ν + c) / Real.sqrt ((ν + c) ^ 2 + x₁ ^ 2)) := by
    apply mul_pos (div_pos (amosFamily_pos ν c hx₁) hx₁)
    rw [sub_pos, div_lt_iff₀ hszpos]
    linarith [hstrict]
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hDz').mono_left
    (nhdsWithin_mono x₁ (fun y hy => ne_of_gt hy))
  have hev_slope : ∀ᶠ y in 𝓝[>] x₁,
      0 < slope D x₁ y :=
    hslope.eventually (eventually_gt_nhds hV_pos)
  have hev_lt : ∀ᶠ y in 𝓝[>] x₁, y < b :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds hb)
  have hex := ((hev_slope.and hev_lt).and self_mem_nhdsWithin).exists
  obtain ⟨m, ⟨hsl, hmb⟩, hm₁⟩ := hex
  refine ⟨m, hm₁, hmb, ?_⟩
  rw [slope_def_field] at hsl
  have hm₁' : (0 : ℝ) < m - x₁ := sub_pos.mpr hm₁
  rcases div_pos_iff.mp hsl with ⟨hnum, _⟩ | ⟨_, hden⟩
  · simp only [hD_def] at hnum hD₁ ⊢
    linarith [hnum, hD₁]
  · linarith [hden, hm₁']

/-- **BLOCK D — uniqueness above the threshold**: two equality
points that both satisfy the STRICT threshold inequality coincide
(the possible degenerate touch exactly at the threshold is the
registered caveat). -/
theorem crossing_unique (ν : ℝ) (hν : 0 ≤ ν) {c x₁ x₂ : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (heq₁ : besselIReal (ν + 1) x₁ / besselIReal ν x₁ = amosFamily ν c x₁)
    (heq₂ : besselIReal (ν + 1) x₂ / besselIReal ν x₂ = amosFamily ν c x₂)
    (hs₁ : ν + c < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + x₁ ^ 2))
    (hs₂ : ν + c < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + x₂ ^ 2)) :
    x₁ = x₂ := by
  -- symmetric auxiliary: a strict crossing strictly below another
  -- crossing is impossible
  have aux : ∀ {y₁ y₂ : ℝ}, 0 < y₁ → 0 < y₂ → y₁ < y₂ →
      besselIReal (ν + 1) y₁ / besselIReal ν y₁ = amosFamily ν c y₁ →
      besselIReal (ν + 1) y₂ / besselIReal ν y₂ = amosFamily ν c y₂ →
      ν + c < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + y₁ ^ 2) → False := by
    intro y₁ y₂ hy₁ hy₂ hlt heqa heqb hstricta
    obtain ⟨m, hm₁, hmb, hDm⟩ :=
      crossing_pos_right ν hν hc1 hy₁ hlt heqa hstricta
    set D : ℝ → ℝ := fun y =>
      besselIReal (ν + 1) y / besselIReal ν y - amosFamily ν c y with hD_def
    have hDy₂ : D y₂ = 0 := by simp only [hD_def]; linarith [heqb]
    have hm0 : 0 < m := lt_trans hy₁ hm₁
    have hcont : ContinuousOn D (Set.Icc m y₂) := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
      exact (((besselRatioReal_hasDerivAt ν hν hy0).sub
        (amosFamily_hasDerivAt ν c hy0)).continuousAt).continuousWithinAt
    set W := {y : ℝ | y ∈ Set.Icc m y₂ ∧ D y ≤ 0} with hW_def
    have hWne : W.Nonempty := ⟨y₂, ⟨le_of_lt hmb, le_refl _⟩, le_of_eq hDy₂⟩
    have hWbdd : BddBelow W := ⟨m, fun y hy => hy.1.1⟩
    have hWclosed : IsClosed W := by
      have : W = Set.Icc m y₂ ∩ D ⁻¹' (Set.Iic 0) := by
        ext y
        simp [hW_def, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
      rw [this]
      exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    set w := sInf W with hw_def
    have hwmem : w ∈ W := hWclosed.csInf_mem hWne hWbdd
    have hwm : m ≤ w := le_csInf hWne (fun y hy => hy.1.1)
    have hw0 : 0 < w := lt_of_lt_of_le hm0 hwm
    have hwne : w ≠ m := by
      intro h
      rw [h] at hwmem
      have h2 := hwmem.2
      simp only [hD_def] at h2
      linarith [h2, hDm]
    have hwm' : m < w := lt_of_le_of_ne hwm (Ne.symm hwne)
    have hleft : ∀ y, m < y → y < w → 0 < D y := by
      intro y h1 h2
      by_contra hy
      push_neg at hy
      have hymem : y ∈ W := by
        refine ⟨⟨le_of_lt h1, ?_⟩, hy⟩
        exact le_of_lt (lt_of_lt_of_le h2 hwmem.1.2)
      exact absurd (csInf_le hWbdd hymem) (not_le.mpr h2)
    have htendsto : Tendsto D (𝓝[<] w) (𝓝 (D w)) :=
      (((besselRatioReal_hasDerivAt ν hν hw0).sub
        (amosFamily_hasDerivAt ν c hw0)).continuousAt).continuousWithinAt
    have hev_ge : ∀ᶠ y in 𝓝[<] w, 0 ≤ D y := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hwm')] with y hy1 hy2
      exact le_of_lt (hleft y hy2 hy1)
    have hDw_ge : 0 ≤ D w := ge_of_tendsto htendsto hev_ge
    have hDw : D w = 0 := le_antisymm hwmem.2 hDw_ge
    have heqw : besselIReal (ν + 1) w / besselIReal ν w = amosFamily ν c w := by
      simp only [hD_def] at hDw
      linarith [hDw]
    -- slope from the left at w is ≤ 0
    have hDw' := crossing_hasDerivAt ν hν hw0 heqw
    have hslope := (hasDerivAt_iff_tendsto_slope.mp hDw').mono_left
      (nhdsWithin_mono w (fun y (hy : y ∈ Set.Iio w) => ne_of_lt hy))
    have hev_slope : ∀ᶠ y in 𝓝[<] w,
        slope D w y ≤ 0 := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hwm')] with y hy1 hy2
      rw [slope_def_field]
      have hDy := hleft y hy2 hy1
      have hyw : y - w < 0 := sub_neg.mpr hy1
      apply le_of_lt
      apply div_neg_of_pos_of_neg
      · simp only [hD_def] at hDy ⊢
        linarith [hDw, hDy]
      · exact hyw
    have hV_le : amosFamily ν c w / w
        * (2 * c - 1 - (ν + c) / Real.sqrt ((ν + c) ^ 2 + w ^ 2)) ≤ 0 :=
      le_of_tendsto hslope hev_slope
    -- but w > y₁ gives the STRICT threshold at w: slope > 0
    have hsw : Real.sqrt ((ν + c) ^ 2 + y₁ ^ 2)
        ≤ Real.sqrt ((ν + c) ^ 2 + w ^ 2) := by
      apply Real.sqrt_le_sqrt
      have hy₁w : y₁ < w := lt_trans hm₁ hwm'
      nlinarith [hy₁w, hy₁]
    have hswpos : 0 < Real.sqrt ((ν + c) ^ 2 + w ^ 2) :=
      Real.sqrt_pos.mpr (by positivity)
    have hfac : 0 < 2 * c - 1 - (ν + c) / Real.sqrt ((ν + c) ^ 2 + w ^ 2) := by
      rw [sub_pos, div_lt_iff₀ hswpos]
      calc ν + c < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + y₁ ^ 2) := hstricta
        _ ≤ (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + w ^ 2) :=
            mul_le_mul_of_nonneg_left hsw (by linarith)
    nlinarith [hV_le, hfac, div_pos (amosFamily_pos ν c hw0) hw0]
  rcases lt_trichotomy x₁ x₂ with h | h | h
  · exact absurd (aux hx₁ hx₂ h heq₁ heq₂ hs₁) not_false
  · exact h
  · exact absurd (aux hx₂ hx₁ h heq₂ heq₁ hs₂) not_false

/-- **BLOCK E1 — orientation after a strict crossing**: past it,
the ratio stays strictly above the family member. -/
theorem crossing_orientation_after (ν : ℝ) (hν : 0 ≤ ν) {c x₁ y : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) (hx₁ : 0 < x₁)
    (heq₁ : besselIReal (ν + 1) x₁ / besselIReal ν x₁ = amosFamily ν c x₁)
    (hs₁ : ν + c < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + x₁ ^ 2))
    (hy : x₁ < y) :
    amosFamily ν c y < besselIReal (ν + 1) y / besselIReal ν y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨m, hm₁, hmy, hDm⟩ :=
    crossing_pos_right ν hν hc1 hx₁ hy heq₁ hs₁
  -- W-argument between m and y produces a left-positive crossing
  -- strictly above x₁, contradicting the strict upward slope there
  set D : ℝ → ℝ := fun z =>
    besselIReal (ν + 1) z / besselIReal ν z - amosFamily ν c z with hD_def
  have hDy_le : D y ≤ 0 := by simp only [hD_def]; linarith [hcon]
  have hm0 : 0 < m := lt_trans hx₁ hm₁
  have hcont : ContinuousOn D (Set.Icc m y) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hm0 hz.1
    exact (((besselRatioReal_hasDerivAt ν hν hz0).sub
      (amosFamily_hasDerivAt ν c hz0)).continuousAt).continuousWithinAt
  set W := {z : ℝ | z ∈ Set.Icc m y ∧ D z ≤ 0} with hW_def
  have hWne : W.Nonempty := ⟨y, ⟨le_of_lt hmy, le_refl _⟩, hDy_le⟩
  have hWbdd : BddBelow W := ⟨m, fun z hz => hz.1.1⟩
  have hWclosed : IsClosed W := by
    have : W = Set.Icc m y ∩ D ⁻¹' (Set.Iic 0) := by
      ext z
      simp [hW_def, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    rw [this]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  set w := sInf W with hw_def
  have hwmem : w ∈ W := hWclosed.csInf_mem hWne hWbdd
  have hwm : m ≤ w := le_csInf hWne (fun z hz => hz.1.1)
  have hw0 : 0 < w := lt_of_lt_of_le hm0 hwm
  have hwne : w ≠ m := by
    intro h
    rw [h] at hwmem
    have h2 := hwmem.2
    simp only [hD_def] at h2
    linarith [h2, hDm]
  have hwm' : m < w := lt_of_le_of_ne hwm (Ne.symm hwne)
  have hleft : ∀ z, m < z → z < w → 0 < D z := by
    intro z h1 h2
    by_contra hz
    push_neg at hz
    have hzmem : z ∈ W := by
      refine ⟨⟨le_of_lt h1, ?_⟩, hz⟩
      exact le_of_lt (lt_of_lt_of_le h2 hwmem.1.2)
    exact absurd (csInf_le hWbdd hzmem) (not_le.mpr h2)
  have htendsto : Tendsto D (𝓝[<] w) (𝓝 (D w)) :=
    (((besselRatioReal_hasDerivAt ν hν hw0).sub
      (amosFamily_hasDerivAt ν c hw0)).continuousAt).continuousWithinAt
  have hev_ge : ∀ᶠ z in 𝓝[<] w, 0 ≤ D z := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hwm')] with z hz1 hz2
    exact le_of_lt (hleft z hz2 hz1)
  have hDw : D w = 0 :=
    le_antisymm hwmem.2 (ge_of_tendsto htendsto hev_ge)
  have heqw : besselIReal (ν + 1) w / besselIReal ν w = amosFamily ν c w := by
    simp only [hD_def] at hDw
    linarith [hDw]
  -- w is a crossing strictly above x₁: strict threshold, so by
  -- uniqueness w = x₁ — contradiction with x₁ < m ≤ w
  have hsw : ν + c < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + w ^ 2) := by
    have h := Real.sqrt_le_sqrt
      (by nlinarith [lt_trans hm₁ hwm', hx₁] :
        (ν + c) ^ 2 + x₁ ^ 2 ≤ (ν + c) ^ 2 + w ^ 2)
    calc ν + c < (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + x₁ ^ 2) := hs₁
      _ ≤ (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + w ^ 2) :=
          mul_le_mul_of_nonneg_left h (by linarith)
  have := crossing_unique ν hν hc1 hc2 hx₁ hw0 heq₁ heqw hs₁ hsw
  linarith [lt_trans hm₁ hwm', this.ge]

/-- **BLOCK E2 — orientation strictly below the threshold**: below
`x_†` the ratio is strictly below the family member (no equality
can occur there by Block C, and the sign is pinned by the small
anchor). -/
theorem crossing_orientation_below (ν : ℝ) (hν : 0 ≤ ν) {c y : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) (hy0 : 0 < y)
    (hbelow : (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + y ^ 2) < ν + c) :
    besselIReal (ν + 1) y / besselIReal ν y < amosFamily ν c y := by
  rcases lt_trichotomy (besselIReal (ν + 1) y / besselIReal ν y)
    (amosFamily ν c y) with h | h | h
  · exact h
  · exact absurd (crossing_threshold ν hν hc1 hc2 hy0 h)
      (not_le.mpr hbelow)
  -- D y > 0: IVT down to the small anchor produces a crossing
  -- strictly below the threshold — contradiction with Block C
  · exfalso
    set a₀ : ℝ := min (Real.sqrt (1 - c)) (y / 2) with ha0_def
    have hsq : 0 < Real.sqrt (1 - c) := Real.sqrt_pos.mpr (by linarith)
    have ha0 : 0 < a₀ := lt_min hsq (by linarith)
    have ha0y : a₀ < y := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    set D : ℝ → ℝ := fun z =>
      besselIReal (ν + 1) z / besselIReal ν z - amosFamily ν c z with hD_def
    have hDa0 : D a₀ < 0 := by
      have h' := crossing_witness_small_le ν hν hc1 hc2 ha0 (min_le_left _ _)
      simp only [hD_def]
      linarith [h']
    have hDy : 0 < D y := by simp only [hD_def]; linarith [h]
    have hcont : ContinuousOn D (Set.Icc a₀ y) := by
      intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le ha0 hz.1
      exact (((besselRatioReal_hasDerivAt ν hν hz0).sub
        (amosFamily_hasDerivAt ν c hz0)).continuousAt).continuousWithinAt
    have h0mem : (0 : ℝ) ∈ Set.Icc (D a₀) (D y) := ⟨le_of_lt hDa0, le_of_lt hDy⟩
    obtain ⟨z, hzmem, hDz⟩ :=
      intermediate_value_Icc (le_of_lt ha0y) hcont h0mem
    have hz0 : 0 < z := lt_of_lt_of_le ha0 hzmem.1
    have heqz : besselIReal (ν + 1) z / besselIReal ν z = amosFamily ν c z := by
      simp only [hD_def] at hDz
      linarith [hDz]
    have hthr := crossing_threshold ν hν hc1 hc2 hz0 heqz
    have hsz : Real.sqrt ((ν + c) ^ 2 + z ^ 2)
        ≤ Real.sqrt ((ν + c) ^ 2 + y ^ 2) := by
      apply Real.sqrt_le_sqrt
      have hzy : z ≤ y := hzmem.2
      nlinarith [hzy, hz0]
    have : ν + c ≤ (2 * c - 1) * Real.sqrt ((ν + c) ^ 2 + y ^ 2) :=
      le_trans hthr (mul_le_mul_of_nonneg_left hsz (by linarith))
    linarith [hbelow, this]

/-- **BLOCK E3 — THE SCALE LAW**: some crossing satisfies the
two-sided explicit localization
`2(ν+c)√(c(1−c)) ≤ (2c−1)·x_* ≤ 2((ν+3/2)² − (ν+c)²)` — both ends
of order `1/(2c−1)` as `c → 1/2⁺`. -/
theorem crossing_scale (ν : ℝ) (hν : 0 ≤ ν) {c : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) :
    ∃ x : ℝ, 0 < x
      ∧ besselIReal (ν + 1) x / besselIReal ν x = amosFamily ν c x
      ∧ 2 * (ν + c) * Real.sqrt (c * (1 - c)) ≤ (2 * c - 1) * x
      ∧ (2 * c - 1) * x ≤ 2 * ((ν + 3 / 2) ^ 2 - (ν + c) ^ 2) := by
  have h2c : (0 : ℝ) < 2 * c - 1 := by linarith
  obtain ⟨x, hxlo, hxhi, heq⟩ := amosFamily_crossing_exists ν hν hc1 hc2
  have hx : 0 < x :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 - c)) hxlo
  refine ⟨x, hx, heq, ?_, ?_⟩
  · -- lower end from Block C: a ≤ (2c−1)s ⟹ (2c−1)x ≥ 2a√(c(1−c))
    have hthr := crossing_threshold ν hν hc1 hc2 hx heq
    set s := Real.sqrt ((ν + c) ^ 2 + x ^ 2) with hs_def
    have hs2 : s ^ 2 = (ν + c) ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
    set σ := Real.sqrt (c * (1 - c)) with hσ_def
    have hσ2 : σ ^ 2 = c * (1 - c) := Real.sq_sqrt (by nlinarith)
    have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
    have ha : (0 : ℝ) < ν + c := by linarith
    -- squares: ((2c−1)x)² ≥ 4a²σ²
    have hsq : (2 * (ν + c) * σ) ^ 2 ≤ ((2 * c - 1) * x) ^ 2 := by
      have h1 : (ν + c) ^ 2 ≤ (2 * c - 1) ^ 2 * s ^ 2 := by
        nlinarith [hthr, ha, h2c]
      nlinarith [h1, hs2, hσ2, h2c]
    nlinarith [hsq, mul_pos h2c hx, mul_nonneg (mul_nonneg
      (by norm_num : (0:ℝ) ≤ 2) ha.le) hσ0, sq_nonneg
      (2 * (ν + c) * σ - (2 * c - 1) * x), sq_nonneg
      (2 * (ν + c) * σ + (2 * c - 1) * x)]
  · -- upper end from the Block-B window
    calc (2 * c - 1) * x
        ≤ (2 * c - 1) * (2 * ((ν + 3 / 2) ^ 2 - (ν + c) ^ 2) / (2 * c - 1)) :=
          mul_le_mul_of_nonneg_left hxhi h2c.le
      _ = 2 * ((ν + 3 / 2) ^ 2 - (ν + c) ^ 2) := by
          field_simp

end AmosClosure
