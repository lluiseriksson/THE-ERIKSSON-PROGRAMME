/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.BesselRealDeriv

/-!
# The Riccati structure at real order (arc C4, phase 3a; charter
Amendment 3)

Mirror of the C3 Riccati layer over the Γ-series objects: the ratio
`ρ_ν = besselIReal (ν+1) / besselIReal ν` satisfies
`ρ' = 1 − ((2ν+1)/x)·ρ − ρ²` for every real `ν ≥ 0`; `amosRHS ν x`
(ALREADY real-parameter in Core) is exactly the positive root of the
real Riccati quadratic; the ψ-formulation and the touch lemma carry
over with `0 ≤ ν` supplying what `Nat.cast_nonneg` supplied before.
-/

namespace AmosClosure

/-- The Riccati quadratic at real order `ν` and argument `x`. -/
noncomputable def riccatiQReal (ν x y : ℝ) : ℝ :=
  1 - (2 * ν + 1) / x * y - y ^ 2

/-- The Bessel ratio at real order. -/
noncomputable def besselRatioReal (ν x : ℝ) : ℝ :=
  besselIReal (ν + 1) x / besselIReal ν x

lemma besselRatioReal_pos {ν : ℝ} (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    0 < besselRatioReal ν x :=
  div_pos (besselIReal_pos (ν + 1) (by linarith) hx)
    (besselIReal_pos ν hν hx)

/-- **The Riccati equation for the real-order Bessel ratio** (phase-3a
target): pure consequence of the phase-1 recurrence and the phase-2
derivative identity. -/
theorem besselRatioReal_hasDerivAt (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (besselRatioReal ν)
      (riccatiQReal ν x (besselRatioReal ν x)) x := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have h0 := besselIReal_pos ν hν hx
  have h0' : besselIReal ν x ≠ 0 := ne_of_gt h0
  have hf := besselIReal_hasDerivAt (ν + 1) (by linarith) hx
  have hg := besselIReal_hasDerivAt ν hν hx
  rw [show ν + 1 + 1 = ν + 2 by ring] at hf
  have hdiv := hf.div hg h0'
  have hrec := besselIReal_recurrence ν hν hx
  have hI2 : besselIReal (ν + 2) x
      = besselIReal ν x - 2 * (ν + 1) / x * besselIReal (ν + 1) x := by
    linarith [hrec]
  rw [hI2] at hdiv
  convert hdiv using 1
  unfold riccatiQReal besselRatioReal
  field_simp
  ring

/-- Positivity of the Amos right-hand side at real order `ν ≥ 0`. -/
lemma amosRHS_pos_of_nonneg {ν : ℝ} (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    0 < amosRHS ν x := by
  unfold amosRHS
  have hs : (0 : ℝ) ≤ Real.sqrt ((ν + 1 / 2) ^ 2 + x ^ 2) :=
    Real.sqrt_nonneg _
  have hden : 0 < ν + 1 / 2 + Real.sqrt ((ν + 1 / 2) ^ 2 + x ^ 2) := by
    linarith
  exact div_pos hx hden

/-- **The calibration identity at real order**: `1/B − B = (2ν+1)/x`
at `B = amosRHS ν x`. -/
lemma amosRHS_calibration_real {ν : ℝ} (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    1 / amosRHS ν x - amosRHS ν x = (2 * ν + 1) / x := by
  unfold amosRHS
  set a : ℝ := ν + 1 / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set s := Real.sqrt (a ^ 2 + x ^ 2) with hs_def
  have hs2 : s ^ 2 = a ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsa : a < s := by nlinarith
  have hsum : 0 < a + s := by linarith
  have hUalt : x / (a + s) = (s - a) / x := by
    rw [div_eq_div_iff (ne_of_gt hsum) (ne_of_gt hx)]
    nlinarith
  have h2a : 2 * ν + 1 = 2 * a := by rw [ha_def]; ring
  rw [one_div_div, hUalt, h2a]
  field_simp
  ring

/-- The Amos RHS is the root of the real Riccati quadratic. -/
lemma riccatiQReal_amosRHS {ν : ℝ} (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    riccatiQReal ν x (amosRHS ν x) = 0 := by
  have hB := amosRHS_pos_of_nonneg hν hx
  have hB' : amosRHS ν x ≠ 0 := ne_of_gt hB
  have hcal := amosRHS_calibration_real hν hx
  unfold riccatiQReal
  have h1 : 1 - amosRHS ν x ^ 2 = (2 * ν + 1) / x * amosRHS ν x := by
    have h := congrArg (fun t => t * amosRHS ν x) hcal
    simp only [sub_mul, one_div, inv_mul_cancel₀ hB'] at h
    nlinarith [h]
  linarith [h1]

/-- `Q(y) > 0` strictly below the root: `0 ≤ y < B`. -/
lemma riccatiQReal_pos_of_lt {ν : ℝ} (hν : 0 ≤ ν) {x y : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) (hyB : y < amosRHS ν x) :
    0 < riccatiQReal ν x y := by
  have hB := amosRHS_pos_of_nonneg hν hx
  have hQB := riccatiQReal_amosRHS hν hx
  have hc : (0 : ℝ) ≤ (2 * ν + 1) / x := by
    apply div_nonneg _ hx.le
    linarith
  unfold riccatiQReal at hQB ⊢
  nlinarith [hQB, hyB, hy, hB, hc]

/-- `ψ_ν(x) = x·(1/ρ_ν(x) − ρ_ν(x))` at real order. -/
noncomputable def besselPsiReal (ν x : ℝ) : ℝ :=
  x * (1 / besselRatioReal ν x - besselRatioReal ν x)

/-- Derivative of `ψ_ν` from the real Riccati equation. -/
lemma besselPsiReal_hasDerivAt (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (besselPsiReal ν)
      ((1 / besselRatioReal ν x - besselRatioReal ν x)
        + x * (-(riccatiQReal ν x (besselRatioReal ν x))
            / besselRatioReal ν x ^ 2
          - riccatiQReal ν x (besselRatioReal ν x))) x := by
  have hρ := besselRatioReal_pos hν hx
  have hρ' : besselRatioReal ν x ≠ 0 := ne_of_gt hρ
  have hR : HasDerivAt (besselRatioReal ν)
      (riccatiQReal ν x (besselRatioReal ν x)) x :=
    besselRatioReal_hasDerivAt ν hν hx
  have hinv : HasDerivAt (fun y => 1 / besselRatioReal ν y)
      (-(riccatiQReal ν x (besselRatioReal ν x))
        / besselRatioReal ν x ^ 2) x := by
    simpa [one_div] using hR.inv hρ'
  have hsub : HasDerivAt
      (fun y => 1 / besselRatioReal ν y - besselRatioReal ν y)
      (-(riccatiQReal ν x (besselRatioReal ν x))
          / besselRatioReal ν x ^ 2
        - riccatiQReal ν x (besselRatioReal ν x)) x := hinv.sub hR
  have hprod := (hasDerivAt_id x).mul hsub
  have hfn2 : (id * fun y => 1 / besselRatioReal ν y - besselRatioReal ν y)
      = fun y : ℝ => y * (1 / besselRatioReal ν y - besselRatioReal ν y) := by
    funext y
    simp [Pi.mul_apply]
  rw [hfn2] at hprod
  simp only [id_eq] at hprod
  have hfun : besselPsiReal ν = fun y =>
      y * (1 / besselRatioReal ν y - besselRatioReal ν y) := rfl
  have hval : (1 / besselRatioReal ν x - besselRatioReal ν x)
      + x * (-(riccatiQReal ν x (besselRatioReal ν x))
          / besselRatioReal ν x ^ 2
        - riccatiQReal ν x (besselRatioReal ν x))
      = 1 * (1 / besselRatioReal ν x - besselRatioReal ν x)
        + x * (-riccatiQReal ν x (besselRatioReal ν x)
            / besselRatioReal ν x ^ 2
          - riccatiQReal ν x (besselRatioReal ν x)) := by ring
  rw [hfun, hval]
  exact hprod

/-- At a touch point `ψ_ν(c) = 2ν+1`, the real Riccati value
vanishes: the ψ-formulation upgrade at real order. -/
lemma riccati_zero_of_real_touch {ν : ℝ} (hν : 0 ≤ ν) {c : ℝ}
    (hc : 0 < c) (htouch : besselPsiReal ν c = 2 * ν + 1) :
    riccatiQReal ν c (besselRatioReal ν c) = 0 := by
  have hρ := besselRatioReal_pos hν hc
  have hρ' : besselRatioReal ν c ≠ 0 := ne_of_gt hρ
  have hc' : c ≠ 0 := ne_of_gt hc
  have heq : 1 / besselRatioReal ν c - besselRatioReal ν c
      = (2 * ν + 1) / c := by
    unfold besselPsiReal at htouch
    rw [eq_div_iff hc']
    nlinarith [htouch]
  unfold riccatiQReal
  rw [← heq]
  field_simp
  ring

end AmosClosure
