/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.AmosLowerReal

/-!
# The crossing phase, block A: the ψ sandwich and the lower half of
the family classification (arc C5, phase 3; charter Amendment 3)

`2ν+1 < ψ_ν(x) < 2ν+2` globally: the lower half is C4's barrier
theorem; the upper half is NEW and cheap — `L_ν > B_{ν,1}`
everywhere (the root sum strictly exceeds `a+b`), so
`ρ_ν > B_{ν,1}`, which by the general calibration is exactly
`ψ_ν < 2ν+2`.  Corollary, killing every `c ≥ 1`: `B_{ν,c}` is a
uniform LOWER bound (RS16's `α ≥ 1` half, machine-checked for
free).  Blocks B–E (existence, threshold, uniqueness, scale) follow
in later commits per the registered plan.
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

/-- **The ψ upper sandwich** (block A headline, NEW):
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

end AmosClosure
