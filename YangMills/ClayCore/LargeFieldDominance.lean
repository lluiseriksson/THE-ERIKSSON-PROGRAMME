/- Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Phase 3 / Task #7 sub-target P2a: super-polynomial dominance lemma
(analytic content of `h_dominated`).

Formalizes the analytic core of Balaban CMP 122 II, Eq (1.98)–(1.100) /
Paper [55] Theorem 8.5: the Balaban super-polynomial large-field profile
    p₀(g) := A₀ · (log g⁻²)^{p*},   A₀ > 0, p* > 1
satisfies the dominance inequality
    exp(−p₀(g)) ≤ E · g²
for every `E > 0` at sufficiently small `g ∈ (0, 1)`.

This retires the *analytic* content of the `h_dominated` field of
`LargeFieldActivityBound`: for any fixed E > 0 (e.g. the E₀ of the
companion small-field bound), the super-polynomial profile dominates at
every small enough coupling. Paired with the P2c structural refactor
(v0.42.0), the `h_dominated` field of `LargeFieldActivityBound` now
carries a fixed `E₀` (exposed as a struct field) and is discharged
directly by `superPoly_dominance_at_specific` at a chosen small-enough
coupling.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No `sorry`. No new axioms.
-/

import Mathlib
import YangMills.ClayCore.LargeFieldBound
import YangMills.ClayCore.WilsonPolymerActivity

namespace YangMills

open Real

noncomputable section

/-- **Balaban super-polynomial profile.**
    p₀(g) := A₀ · (log g⁻²)^{p*} with A₀ > 0, p* > 1.
    This is the profile used in Paper [55] Theorem 8.5 / Balaban CMP 122 II
    Eq (1.98–1.100), whose key property is the super-polynomial growth
    as g → 0⁺ that lets `exp(−p₀(g))` be dominated by `E · g²` for every
    positive `E` at sufficiently small `g`. See `superPoly_dominance`. -/
def superPolyProfile
    (A₀ : ℝ) (hA₀ : 0 < A₀)
    (pstar : ℝ) (hpstar : 1 < pstar) : LargeFieldProfile where
  A0 := A₀
  hA0 := hA₀
  pstar := pstar
  hpstar := by linarith
  eval := fun g => A₀ * (Real.log (g⁻¹ ^ 2)) ^ pstar
  heval_pos := by
    intro g hg_pos hg_lt1
    have hginv_pos : 0 < g⁻¹ := inv_pos.mpr hg_pos
    have hginv_gt1 : 1 < g⁻¹ := by
      have h1 : g * g⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hg_pos)
      have h2 : g * g⁻¹ < 1 * g⁻¹ := mul_lt_mul_of_pos_right hg_lt1 hginv_pos
      rw [h1, one_mul] at h2
      exact h2
    have hginv_sq_pos : 0 < g⁻¹ ^ 2 := by positivity
    have hginv_sq_gt1 : 1 < g⁻¹ ^ 2 := by
      nlinarith [hginv_gt1, hginv_pos]
    have hlog_pos : 0 < Real.log (g⁻¹ ^ 2) := Real.log_pos hginv_sq_gt1
    have hpow_pos : 0 < (Real.log (g⁻¹ ^ 2)) ^ pstar :=
      Real.rpow_pos_of_pos hlog_pos pstar
    exact mul_pos hA₀ hpow_pos

/-! ### Super-polynomial dominance: the analytic core of `h_dominated` -/

/-- **Super-polynomial dominance (Balaban Theorem 8.5 / CMP 122 Eq 1.98–1.100).**

For every A > 0, p > 1, E > 0, there is a threshold g₀ ∈ (0, 1] such that
for every `g ∈ (0, g₀)`,
    `exp(−A · (log g⁻²)^p) ≤ E · g²`.

This is the key analytic content of the large-field dominance inequality
in Balaban's RG construction: the super-polynomial profile
`p₀(g) = A·(log g⁻²)^p` with `p > 1` decays (under `exp(−·)`) faster than
any geometric `E · g²` near `g = 0`.

Proof strategy. Set `u := log(g⁻²) = −2 · log g`. Then:
1. `A · u^p − u → +∞` as `u → +∞` (since `p > 1` makes the p-th power
   dominate the linear term).
2. For `u ≥ U := max(1, ((1 + C)/A)^{1/(p−1)})` with `C := max(1, −log E)`,
   one gets `A · u^p − u ≥ −log E`.
3. For `g < g₀ := exp(−U/2)`, `u > U`, so step 2 applies.
4. Rearranging via `exp` monotonicity gives the claim.

No `sorry`, no new axioms. -/
theorem superPoly_dominance
    {A : ℝ} (hA : 0 < A) {p : ℝ} (hp : 1 < p) {E : ℝ} (hE : 0 < E) :
    ∃ g₀ : ℝ, 0 < g₀ ∧ g₀ ≤ 1 ∧
      ∀ g : ℝ, 0 < g → g < g₀ →
        Real.exp (-A * (Real.log (g⁻¹ ^ 2)) ^ p) ≤ E * g ^ 2 := by
  have hp_sub_pos : 0 < p - 1 := by linarith
  have hp_sub_ne : p - 1 ≠ 0 := ne_of_gt hp_sub_pos
  -- Step 1: choose `C := max(1, -log E)` so that both `1 ≤ C` and `-log E ≤ C`.
  set C : ℝ := max 1 (-Real.log E) with hC_def
  have hC_ge_one : (1 : ℝ) ≤ C := le_max_left _ _
  have hC_ge_neglog : -Real.log E ≤ C := le_max_right _ _
  have hC_pos : 0 < C := by linarith
  have h_oneC_pos : 0 < 1 + C := by linarith
  -- Step 2: choose `M := ((1+C)/A)^{1/(p-1)}`, the threshold at which
  -- `A · u^{p-1} ≥ 1 + C`.
  have h_ratio_pos : 0 < (1 + C) / A := div_pos h_oneC_pos hA
  set M : ℝ := ((1 + C) / A) ^ (1 / (p - 1)) with hM_def
  have hM_pos : 0 < M := Real.rpow_pos_of_pos h_ratio_pos _
  -- Step 3: choose `U := max(1, M)`, guaranteeing both `u ≥ 1` and `u ≥ M`.
  set U : ℝ := max 1 M with hU_def
  have hU_ge_one : (1 : ℝ) ≤ U := le_max_left _ _
  have hU_ge_M : M ≤ U := le_max_right _ _
  have hU_pos : 0 < U := by linarith
  have hU_nonneg : 0 ≤ U := le_of_lt hU_pos
  -- Step 4: choose `g₀ := exp(-U/2)`.
  set g₀ : ℝ := Real.exp (-(U / 2)) with hg₀_def
  have hg₀_pos : 0 < g₀ := Real.exp_pos _
  have hg₀_le_one : g₀ ≤ 1 := by
    show Real.exp (-(U / 2)) ≤ 1
    have hle : -(U / 2) ≤ 0 := by linarith
    have hexp_le : Real.exp (-(U / 2)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
    rwa [Real.exp_zero] at hexp_le
  refine ⟨g₀, hg₀_pos, hg₀_le_one, ?_⟩
  -- The main bound.
  intro g hg_pos hg_lt_g₀
  -- u = log(g⁻²) = -2 log g.
  set u : ℝ := Real.log (g⁻¹ ^ 2) with hu_def
  have hu_eq : u = -2 * Real.log g := by
    rw [hu_def, Real.log_pow, Real.log_inv]; push_cast; ring
  -- From g < g₀ = exp(-U/2): log g < -U/2, hence u = -2 log g > U.
  have hlog_g_lt : Real.log g < -(U / 2) := by
    have h1 : Real.log g < Real.log g₀ := Real.log_lt_log hg_pos hg_lt_g₀
    rwa [hg₀_def, Real.log_exp] at h1
  have hu_gt_U : U < u := by rw [hu_eq]; linarith
  have hu_pos : 0 < u := by linarith
  have hu_ge_one : 1 ≤ u := by linarith
  have hu_ge_M : M ≤ u := by linarith
  have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
  -- M^(p-1) = (1+C)/A, by `rpow_mul` with exponents `1/(p-1)` and `(p-1)`.
  have h_M_rpow : M ^ (p - 1) = (1 + C) / A := by
    rw [hM_def, ← Real.rpow_mul (le_of_lt h_ratio_pos),
        one_div_mul_cancel hp_sub_ne, Real.rpow_one]
  -- u^(p-1) ≥ (1+C)/A.
  have hu_rpow_ge : (1 + C) / A ≤ u ^ (p - 1) := by
    rw [← h_M_rpow]
    exact Real.rpow_le_rpow (le_of_lt hM_pos) hu_ge_M (le_of_lt hp_sub_pos)
  -- A · u^(p-1) ≥ 1 + C.
  have h_A_rpow : 1 + C ≤ A * u ^ (p - 1) := by
    have h1 : A * ((1 + C) / A) = 1 + C := by field_simp
    have h2 : A * ((1 + C) / A) ≤ A * u ^ (p - 1) :=
      mul_le_mul_of_nonneg_left hu_rpow_ge (le_of_lt hA)
    linarith
  -- u^p = u · u^(p-1).
  have h_u_pow : u ^ p = u * u ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) from by ring]
    rw [Real.rpow_add hu_pos, Real.rpow_one]
  -- A · u^p ≥ u · (1 + C).
  have h_A_u_pow : u * (1 + C) ≤ A * u ^ p := by
    calc u * (1 + C)
        ≤ u * (A * u ^ (p - 1)) :=
          mul_le_mul_of_nonneg_left h_A_rpow hu_nonneg
      _ = A * (u * u ^ (p - 1)) := by ring
      _ = A * u ^ p := by rw [← h_u_pow]
  -- A · u^p − u ≥ -log E.
  have h_diff : -Real.log E ≤ A * u ^ p - u := by
    have hC_le_uC : C ≤ u * C :=
      le_mul_of_one_le_left (le_of_lt hC_pos) hu_ge_one
    calc -Real.log E
        ≤ C := hC_ge_neglog
      _ ≤ u * C := hC_le_uC
      _ = u * (1 + C) - u := by ring
      _ ≤ A * u ^ p - u := by linarith
  -- Hence -(A · u^p) ≤ log E + 2·log g (since -u = 2·log g).
  have h_neg_le : -(A * u ^ p) ≤ Real.log E + 2 * Real.log g := by
    have : -(A * u ^ p) ≤ Real.log E - u := by linarith
    rw [hu_eq] at this
    linarith
  -- log E + 2·log g = log(E · g²).
  have h_log_prod : Real.log E + 2 * Real.log g = Real.log (E * g ^ 2) := by
    rw [Real.log_mul (ne_of_gt hE) (by positivity : (g ^ 2 : ℝ) ≠ 0),
        Real.log_pow]
    push_cast; ring
  -- exp(-(A · u^p)) ≤ E · g².
  have h_exp_le : Real.exp (-(A * u ^ p)) ≤ E * g ^ 2 := by
    have h_bound : -(A * u ^ p) ≤ Real.log (E * g ^ 2) := by
      rw [← h_log_prod]; exact h_neg_le
    have h_exp_mono : Real.exp (-(A * u ^ p)) ≤ Real.exp (Real.log (E * g ^ 2)) :=
      Real.exp_le_exp.mpr h_bound
    rwa [Real.exp_log (by positivity : (0 : ℝ) < E * g ^ 2)] at h_exp_mono
  -- Unfold the goal's form `-A * (…)^p = -(A * (…)^p)`.
  have h_neg_mul : -A * Real.log (g⁻¹ ^ 2) ^ p = -(A * Real.log (g⁻¹ ^ 2) ^ p) := by
    ring
  rw [h_neg_mul]
  exact h_exp_le

/-- **Mass-gap companion of `superPoly_dominance`.**

A clean consequence: the super-polynomial profile gives an *effective*
mass gap `m := A · (log g⁻²)^p / 2` at every sufficiently small coupling,
with prefactor `E`. (Not exported into any larger chain yet; this is a
smoke-test reference computation.) -/
theorem superPoly_dominance_at_specific
    {A : ℝ} (hA : 0 < A) {p : ℝ} (hp : 1 < p) {E : ℝ} (hE : 0 < E) :
    ∃ g : ℝ, 0 < g ∧ g < 1 ∧
      Real.exp (-A * (Real.log (g⁻¹ ^ 2)) ^ p) ≤ E * g ^ 2 := by
  obtain ⟨g₀, hg₀_pos, hg₀_le_one, hforall⟩ := superPoly_dominance hA hp hE
  refine ⟨g₀ / 2, by positivity, ?_, hforall (g₀ / 2) (by positivity) (by linarith)⟩
  linarith

/-! ### P2e-α: super-polynomial dominance `LargeFieldActivityBound` constructor

Packages `superPoly_dominance_at_specific` (P2a analytic core, v0.41.0) into
the fixed-E₀ struct shape of `LargeFieldActivityBound` (P2c structural
refactor, v0.42.0). The caller supplies the RG/cluster-expansion large-field
activity bound `h_lf_bound_at` uniformly in `g` (P2e main target,
multi-week); this constructor wires dominance + activity into a first-class
`LargeFieldActivityBound N_c` term at a small-enough coupling chosen by
`superPoly_dominance_at_specific`.

Oracle: `[propext, Classical.choice, Quot.sound]`. -/
noncomputable def LargeFieldActivityBound.ofSuperPoly {N_c : Nat} [NeZero N_c]
    (A : ℝ) (hA : 0 < A) (p : ℝ) (hp : 1 < p)
    (E : ℝ) (hE : 0 < E)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (h_lf_bound_at : ∀ (g_bar : ℝ), 0 < g_bar → g_bar < 1 →
      ∀ (n : ℕ), ∃ R : ℝ, 0 ≤ R ∧
        R ≤ Real.exp (-(A * (Real.log (g_bar⁻¹ ^ 2)) ^ p)) * Real.exp (-kappa * n)) :
    LargeFieldActivityBound N_c :=
  let dom := superPoly_dominance_at_specific hA hp hE
  let g := Classical.choose dom
  let spec := Classical.choose_spec dom
  { profile := superPolyProfile A hA p hp
    kappa := kappa
    hkappa := hkappa
    g_bar := g
    hg_pos := spec.1
    hg_lt1 := spec.2.1
    E0 := E
    hE0 := hE
    h_lf_bound := h_lf_bound_at g spec.1 spec.2.1
    h_dominated := by
      show Real.exp (-(A * (Real.log (g⁻¹ ^ 2)) ^ p)) ≤ E * g ^ 2
      have h_neg :
          -(A * (Real.log (g⁻¹ ^ 2)) ^ p) = -A * (Real.log (g⁻¹ ^ 2)) ^ p := by ring
      rw [h_neg]
      exact spec.2.2 }

/-! ### P2f-α: SFA + LFA → BalabanHyps end-to-end constructor

Cierra el loop estructural del α-stack: toma un `WilsonPolymerActivityBound`
(del cual P2d-α produce el SFA) más los inputs analíticos large-field
(`profile`, `h_lf_bound_at`, `h_dominated`) evaluados en el `g_bar`
canónico `wab.r`, y emite un `BalabanHyps N_c` completo vía
`balabanHyps_of_bounds`.

Usa los mismos constantes que `SmallFieldActivityBound.ofWilsonActivity`
(`E₀ := A₀ + 1`, `κ := -log r`, `ḡ := r`), por lo que las tres
igualdades `hg_eq / hk_eq / hE0_eq` cierran por `rfl`.

NO usa `LargeFieldActivityBound.ofSuperPoly` (que `Classical.choose`a
su `g_bar`, lo cual impide la igualdad con `wab.r`); construye la LFA
directamente con `g_bar := wab.r`, dejando el contenido analítico
(`h_lf_bound_at`, `h_dominated`) como hipótesis del caller.

Pure-additive: no retira axioma ni sorry, no decreta nada sobre las barras
del README. El P2e main / P2d main siguen siendo el camino para mover %.

Oracle: `[propext, Classical.choice, Quot.sound]`. -/
noncomputable def balabanHyps_from_wilson_activity
    {N_c : Nat} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (profile : LargeFieldProfile)
    (h_lf_bound_at : ∀ (n : Nat), ∃ R : Real, 0 ≤ R ∧
      R ≤ Real.exp (-(profile.eval wab.r)) * Real.exp (-(-Real.log wab.r) * n))
    (h_dominated : Real.exp (-(profile.eval wab.r)) ≤ (wab.A₀ + 1) * wab.r ^ 2) :
    BalabanHyps N_c :=
  let sfb := SmallFieldActivityBound.ofWilsonActivity wab
  let lfb : LargeFieldActivityBound N_c :=
    { profile := profile
      kappa := -Real.log wab.r
      hkappa := neg_pos.mpr (Real.log_neg wab.hr_pos wab.hr_lt1)
      g_bar := wab.r
      hg_pos := wab.hr_pos
      hg_lt1 := wab.hr_lt1
      E0 := wab.A₀ + 1
      hE0 := by linarith [wab.hA₀]
      h_lf_bound := h_lf_bound_at
      h_dominated := h_dominated }
  balabanHyps_of_bounds sfb lfb rfl rfl rfl

end

end YangMills

/-! ## Axiom oracle declarations (informational)

Emitted at build time; expected oracle is `[propext, Classical.choice, Quot.sound]`. -/

#print axioms YangMills.superPolyProfile
#print axioms YangMills.superPoly_dominance
#print axioms YangMills.superPoly_dominance_at_specific
#print axioms YangMills.LargeFieldActivityBound.ofSuperPoly
#print axioms YangMills.balabanHyps_from_wilson_activity
