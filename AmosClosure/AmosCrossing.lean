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

/-- Small-side witness (charter Amendment 2): at `x₋ = √(1−c)`,
uniformly in `ν ≥ 0`, the ratio is strictly below `B_{ν,c}`. -/
lemma crossing_witness_small (ν : ℝ) (hν : 0 ≤ ν) {c : ℝ}
    (hc1 : 1 / 2 < c) (hc2 : c < 1) :
    besselIReal (ν + 1) (Real.sqrt (1 - c)) / besselIReal ν (Real.sqrt (1 - c))
      < amosFamily ν c (Real.sqrt (1 - c)) := by
  set x := Real.sqrt (1 - c) with hx_def
  have hx2 : x ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  have hx : 0 < x := Real.sqrt_pos.mpr (by linarith)
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
      rcases eq_or_lt_of_le (le_of_eq hx2.symm) with _ | _
      · rw [div_lt_iff₀ (by linarith)]
        nlinarith [hx2]
      · rw [div_lt_iff₀ (by linarith)]
        nlinarith [hx2]
    -- the registered arithmetic: (x²/2)(1/(ν+c) + (ν+1)/(ν+2)) < 2(1−c)
    have harith : x ^ 2 / (2 * (ν + c))
        + 2 * (ν + 1) * ((x / 2) ^ 2 / (ν + 2)) < 2 * (1 - c) := by
      have hxc : x ^ 2 = 1 - c := hx2
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
    have h := crossing_witness_small ν hν hc1 hc2
    rw [← hxm_def] at h
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

end AmosClosure
