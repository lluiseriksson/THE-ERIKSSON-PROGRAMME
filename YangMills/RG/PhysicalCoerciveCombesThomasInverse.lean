/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalCoerciveCombesThomas
import YangMills.RG.CoerciveCovariance

/-!
# Coercive Combes–Thomas: tilted inverse and kernel extraction — CT3 + CT4
(`hRpoly` campaign — P4-CT ladder, `docs/HRPOLY-CAMPAIGN-PLAN.md` §3ter)

CT1+CT2 (`PhysicalCoerciveCombesThomas.lean`) proved that tilting a coercive
finite-range operator `K` by `T_θ` rooted at `r` keeps it coercive with
constant `c − M(e^{θR}−1)N_R`.  This module finishes the generic ladder:

**CT3 (tilted inverse at the θ-budget).**  Under the budget
`M(e^{θR}−1)N_R ≤ c/2` the tilted operator `K_θ` is coercive with constant
`c/2` (`isCoerciveCLM_physicalTiltConj_half`), hence
`covarianceOfIsCoerciveCLM` gives a two-sided inverse with norm `≤ 2/c`
(`exists_physicalTiltConj_inverse_of_budget`).

**CT4 (kernel extraction at `r := source`).**  For ANY right inverse `C` of
`K` (`K ∘ C = id`), rooting the tilt at the probe bond `p` gives
`C δ_p v = T_{−θ}(y)` with `y := T_θ(C δ_p v)` satisfying `K_θ y = δ_p v`
(the probe is a fixed point of its own tilt, `dist p p = 0`), so coercivity
of `K_θ` at `c/2` bounds `‖y‖ ≤ (2/c)‖v‖` and the entry at `q` picks up the
factor `e^{−θ·dist p q}`:

`PhysicalCovarianceExponentialKernelBound C dist (2/c) θ`

(`physicalCovariance_exponentialKernelBound_of_coercive`) — exactly the
`hkernel` shape of `PhysicalLocalizedCovarianceCertificate`.

**The positive-tilt witness.**  `exists_pos_tiltBudget`: for every `c > 0`
there is an EXPLICIT `θ > 0` meeting the budget, namely
`θ = log(1 + c/(2·M·N_R))/(R+1)` (and any `θ` when `M·N_R = 0`).

**Honest scope.**  Generic in the operator: the instantiation on the flat
physical shell (`flatGaugeFixedCovarianceCLM` with the proved stencils and
the fixed-volume Poincaré constant — the `CT_fixedVolume` endpoint) is the
next brick.  All constants fixed-volume; the §3ter volume-uniformity guard
applies.  Nothing here touches the interacting integral (G5), `hRpoly`,
mass gap, or Clay.

**Source.**  Combes–Thomas (CMP 34, 1973); Bałaban propagator bounds
(CMP 95/99) as the target application; strategy/framing Lluis Eriksson.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

variable {d N Nc : ℕ} [NeZero N]

/-- Coercivity is monotone (downward) in the constant. -/
theorem IsCoerciveCLM.mono_const
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →L[ℝ] E} {c c' : ℝ} (h : IsCoerciveCLM A c) (hle : c' ≤ c) :
    IsCoerciveCLM A c' := fun x =>
  le_trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (h x)

/-- **CT3 coercivity at the θ-budget**: under `M(e^{θR}−1)N_R ≤ c/2` the
tilted operator keeps HALF the coercivity constant. -/
theorem isCoerciveCLM_physicalTiltConj_half
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    {θ : ℝ} (hθ : 0 ≤ θ) (r : PhysicalBond d N) {R NR : ℕ} {M c : ℝ}
    (hM : 0 ≤ M)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hcoer : IsCoerciveCLM K c)
    (hbudget : M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c / 2) :
    IsCoerciveCLM (physicalTiltConjCLM (Nc := Nc) dist θ r K) (c / 2) :=
  (isCoerciveCLM_physicalTiltConj dist hsymm htri hθ r hM hNR hrange
    hbound hcoer).mono_const (by linarith)

/-- **CT3 — the tilted inverse at the θ-budget**: `K_θ` has a two-sided
continuous linear inverse of norm at most `2/c`, produced by
`covarianceOfIsCoerciveCLM` from the surviving coercivity constant `c/2`. -/
theorem exists_physicalTiltConj_inverse_of_budget
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    {θ : ℝ} (hθ : 0 ≤ θ) (r : PhysicalBond d N) {R NR : ℕ} {M c : ℝ}
    (hM : 0 ≤ M) (hcpos : 0 < c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hcoer : IsCoerciveCLM K c)
    (hbudget : M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c / 2) :
    ∃ Cθ : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc,
      Cθ.comp (physicalTiltConjCLM (Nc := Nc) dist θ r K) =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc) ∧
      (physicalTiltConjCLM (Nc := Nc) dist θ r K).comp Cθ =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc) ∧
      ‖Cθ‖ ≤ 2 / c := by
  have hcoerθ : IsCoerciveCLM (physicalTiltConjCLM (Nc := Nc) dist θ r K)
      (c / 2) :=
    isCoerciveCLM_physicalTiltConj_half dist hsymm htri hθ r hM hNR hrange
      hbound hcoer hbudget
  refine ⟨covarianceOfIsCoerciveCLM _ (half_pos hcpos) hcoerθ,
    covarianceOfIsCoerciveCLM_comp_precision _ (half_pos hcpos) hcoerθ,
    precision_comp_covarianceOfIsCoerciveCLM _ (half_pos hcpos) hcoerθ, ?_⟩
  have hnorm := norm_covarianceOfIsCoerciveCLM_le _ (half_pos hcpos) hcoerθ
  rwa [inv_div] at hnorm

/-- The probe at the tilt root is a fixed point of its own tilt
(`dist r r = 0`). -/
theorem physicalTiltCLM_single_root
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (r : PhysicalBond d N) (v : SUNLieCoord Nc)
    (hself : dist r r = 0) :
    physicalTiltCLM (Nc := Nc) dist θ r
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) r v) =
      singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) r v := by
  apply PiLp.ext
  intro q
  by_cases hq : q = r
  · subst hq
    simp [physicalTiltCLM_apply, hself]
  · simp [physicalTiltCLM_apply,
      singlePhysicalBondCochain_of_ne (v := v) hq]

/-- **CT4 exact untilt identity at `r := source`** (owner obligation (5),
first half): every covariance entry untilts EXACTLY —
`(C δ_p v) q = e^{−θ·dist p q} · (T_θ (C δ_p v)) q`.  No hypotheses on `C`:
this is the pure tilt algebra rooted at the probe bond. -/
theorem physicalCovariance_entry_untilt
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (C : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc)
    (p q : PhysicalBond d N) (v : SUNLieCoord Nc) :
    C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q =
      Real.exp (-θ * (dist p q : ℝ)) •
        physicalTiltCLM (Nc := Nc) dist θ p
          (C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v)) q := by
  have huntilt : physicalTiltCLM (Nc := Nc) dist (-θ) p
      (physicalTiltCLM (Nc := Nc) dist θ p
        (C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))) =
      C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) :=
    ContinuousLinearMap.ext_iff.mp
      (physicalTiltCLM_neg_comp (Nc := Nc) dist θ p) _
  conv_lhs => rw [← huntilt]
  exact physicalTiltCLM_apply dist (-θ) p q _

/-- **CT4 tilted-probe identity at `r := source`** (owner obligation (5),
second half): `y := T_θ(C δ_p v)` is EXACTLY the tilted-inverse image of
the probe — `K_θ y = δ_p v`.  Combined with the untilt identity this is the
exact statement `K⁻¹δ_p(q) = e^{−θ·dist p q}·(K_θ⁻¹ δ_p)(q)`. -/
theorem physicalTiltConj_tilted_probe
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hself : ∀ p, dist p p = 0) (θ : ℝ)
    {K C : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hKC : K.comp C = ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc))
    (p : PhysicalBond d N) (v : SUNLieCoord Nc) :
    physicalTiltConjCLM (Nc := Nc) dist θ p K
        (physicalTiltCLM (Nc := Nc) dist θ p
          (C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))) =
      singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v := by
  have huntilt : physicalTiltCLM (Nc := Nc) dist (-θ) p
      (physicalTiltCLM (Nc := Nc) dist θ p
        (C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))) =
      C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) :=
    ContinuousLinearMap.ext_iff.mp
      (physicalTiltCLM_neg_comp (Nc := Nc) dist θ p) _
  have hKCy : K (C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))
      = singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v :=
    ContinuousLinearMap.ext_iff.mp hKC _
  unfold physicalTiltConjCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    huntilt, hKCy]
  exact physicalTiltCLM_single_root dist θ p v (hself p)

/-- **CT4 — Combes–Thomas kernel extraction at `r := source`**: any right
inverse `C` of a coercive finite-range operator `K` satisfies the
source-facing exponential kernel bound
`‖(C δ_p v) q‖ ≤ (2/c)·e^{−θ·dist q p}·‖v‖`, i.e.
`PhysicalCovarianceExponentialKernelBound C dist (2/c) θ`, whenever the
θ-budget `M(e^{θR}−1)N_R ≤ c/2` holds with `θ > 0`. -/
theorem physicalCovariance_exponentialKernelBound_of_coercive
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (hself : ∀ p, dist p p = 0)
    {θ : ℝ} (hθ : 0 < θ) {R NR : ℕ} {M c : ℝ}
    (hM : 0 ≤ M) (hcpos : 0 < c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {K C : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hcoer : IsCoerciveCLM K c)
    (hKC : K.comp C = ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc))
    (hbudget : M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c / 2) :
    PhysicalCovarianceExponentialKernelBound C dist (2 / c) θ := by
  refine ⟨by positivity, hθ, ?_⟩
  intro p q v
  -- the tilt is rooted at the SOURCE bond p
  have hcoerθ : IsCoerciveCLM (physicalTiltConjCLM (Nc := Nc) dist θ p K)
      (c / 2) :=
    isCoerciveCLM_physicalTiltConj_half dist hsymm htri hθ.le p hM hNR hrange
      hbound hcoer hbudget
  set δp : PhysicalGaugeOneCochain d N Nc :=
    singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v with hδp
  set y : PhysicalGaugeOneCochain d N Nc :=
    physicalTiltCLM (Nc := Nc) dist θ p (C δp) with hy
  -- the tilted operator maps y back to the probe
  have huntilt : physicalTiltCLM (Nc := Nc) dist (-θ) p y = C δp := by
    rw [hy]
    exact ContinuousLinearMap.ext_iff.mp
      (physicalTiltCLM_neg_comp (Nc := Nc) dist θ p) (C δp)
  have hKCy : K (C δp) = δp := ContinuousLinearMap.ext_iff.mp hKC δp
  have hKθy : physicalTiltConjCLM (Nc := Nc) dist θ p K y = δp := by
    unfold physicalTiltConjCLM
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      huntilt, hKCy]
    exact physicalTiltCLM_single_root dist θ p v (hself p)
  -- coercivity of the tilted operator bounds the tilted image
  have hynorm : ‖y‖ ≤ 2 / c * ‖v‖ := by
    have hcoer_y := hcoerθ y
    rw [hKθy] at hcoer_y
    have hinner : inner ℝ y δp ≤ ‖y‖ * ‖δp‖ := real_inner_le_norm y δp
    have hδpnorm : ‖δp‖ = ‖v‖ := norm_singlePhysicalBondCochain p v
    by_cases hy0 : ‖y‖ = 0
    · rw [hy0]
      positivity
    · have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
      have hchain : c / 2 * ‖y‖ ^ 2 ≤ ‖y‖ * ‖v‖ := by
        calc c / 2 * ‖y‖ ^ 2 ≤ inner ℝ y δp := hcoer_y
          _ ≤ ‖y‖ * ‖δp‖ := hinner
          _ = ‖y‖ * ‖v‖ := by rw [hδpnorm]
      have h2 : c * ‖y‖ ≤ 2 * ‖v‖ := by
        nlinarith [hchain, hypos]
      rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
      linarith
  -- untilt the entry: the target picks up the decaying factor
  have hentry : C δp q = Real.exp (-θ * (dist p q : ℝ)) • y q := by
    rw [← huntilt]
    exact physicalTiltCLM_apply dist (-θ) p q y
  calc ‖C δp q‖
      = Real.exp (-θ * (dist p q : ℝ)) * ‖y q‖ := by
        rw [hentry, norm_smul, Real.norm_eq_abs, Real.abs_exp]
    _ ≤ Real.exp (-θ * (dist p q : ℝ)) * ‖y‖ := by
        apply mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ q)
          (Real.exp_pos _).le
    _ ≤ Real.exp (-θ * (dist p q : ℝ)) * (2 / c * ‖v‖) := by
        apply mul_le_mul_of_nonneg_left hynorm (Real.exp_pos _).le
    _ = 2 / c * Real.exp (-(θ * (dist q p : ℝ))) * ‖v‖ := by
        rw [hsymm p q, neg_mul]
        ring

/-- **The positive-tilt witness**: for every positive coercivity constant
there is an explicit POSITIVE tilt rate meeting the θ-budget —
`θ = log(1 + c/(2·M·N_R))/(R+1)` when `M·N_R > 0`, any positive `θ`
otherwise. -/
theorem exists_pos_tiltBudget (R NR : ℕ) {M c : ℝ} (hM : 0 ≤ M)
    (hc : 0 < c) :
    ∃ θ : ℝ, 0 < θ ∧
      M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c / 2 := by
  by_cases hB : M * (NR : ℝ) = 0
  · refine ⟨1, one_pos, ?_⟩
    have hz : M * (Real.exp (1 * (R : ℝ)) - 1) * (NR : ℝ)
        = (Real.exp (1 * (R : ℝ)) - 1) * (M * (NR : ℝ)) := by ring
    rw [hz, hB, mul_zero]
    positivity
  · have hBpos : 0 < M * (NR : ℝ) :=
      lt_of_le_of_ne (by positivity) (Ne.symm hB)
    set B := M * (NR : ℝ) with hBdef
    have harg : (0:ℝ) < 1 + c / (2 * B) := by positivity
    have hlogpos : 0 < Real.log (1 + c / (2 * B)) := by
      apply Real.log_pos
      have : 0 < c / (2 * B) := by positivity
      linarith
    refine ⟨Real.log (1 + c / (2 * B)) / ((R : ℝ) + 1), by positivity, ?_⟩
    set θ0 : ℝ := Real.log (1 + c / (2 * B)) / ((R : ℝ) + 1) with hθ0
    have hR1 : (0:ℝ) < (R : ℝ) + 1 := by positivity
    have hθR : θ0 * (R : ℝ) ≤ Real.log (1 + c / (2 * B)) := by
      rw [hθ0, div_mul_eq_mul_div, div_le_iff₀ hR1]
      have hRle : (R : ℝ) ≤ (R : ℝ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_left hRle hlogpos.le
    have hexp : Real.exp (θ0 * (R : ℝ)) ≤ 1 + c / (2 * B) := by
      have h2 := Real.exp_le_exp.mpr hθR
      rwa [Real.exp_log harg] at h2
    have hclear : c / (2 * B) * B = c / 2 := by
      have hBne : B ≠ 0 := ne_of_gt hBpos
      field_simp
    have hstep : (Real.exp (θ0 * (R : ℝ)) - 1) * B ≤ c / 2 := by
      have h3 : (Real.exp (θ0 * (R : ℝ)) - 1) * B ≤ c / (2 * B) * B := by
        apply mul_le_mul_of_nonneg_right _ hBpos.le
        linarith
      linarith [hclear, h3]
    have hfin : M * (Real.exp (θ0 * (R : ℝ)) - 1) * (NR : ℝ)
        = (Real.exp (θ0 * (R : ℝ)) - 1) * B := by
      rw [hBdef]
      ring
    rw [hfin]
    exact hstep

end YangMills.RG
