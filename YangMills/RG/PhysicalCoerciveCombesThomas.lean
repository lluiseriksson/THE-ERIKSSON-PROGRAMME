/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalGaugeCovarianceLocalization
import YangMills.RG.CoercivePerturbation

/-!
# Coercive Combes–Thomas on physical gauge cochains — CT1 + CT2
(`hRpoly` campaign — P4-CT ladder, `docs/HRPOLY-CAMPAIGN-PLAN.md` §3ter)

The Neumann-series decay engine (`KernelDecay.lean`) only reaches operators
that are entrywise SMALL.  The actual flat physical precision operator is
Laplacian-type: invertible by COERCIVITY, not smallness.  This module builds
the weighted-conjugation (Combes–Thomas) route directly on the PHYSICAL
cochain space `PhysicalGaugeOneCochain d N Nc` — the same type, probes
(`singlePhysicalBondCochain`), and predicates
(`PhysicalCovarianceFiniteRange`, `PhysicalCovarianceKernelBound`) that the
localization API (`PhysicalGaugeCovarianceLocalization.lean`) consumes — so
that the CT4 endpoint can instantiate LITERALLY on
`flatGaugeFixedPrecisionCLM` / `flatGaugeFixedCovarianceCLM` with no
translation layer.

**CT1 (tilt algebra).**  `physicalTiltCLM dist θ r` multiplies the cochain at
bond `q` by `e^{θ·dist r q}`.  Tilts compose additively, `θ = 0` is the
identity, and conjugation `K_θ := T_θ ∘ K ∘ T_{−θ}` acts on kernel entries by
`e^{θ(dist r q − dist r p)}`; for a symmetric triangle distance and kernel
range `R` this factor is at most `e^{θR}` on the support, so range is
preserved and the entrywise bound degrades only by `e^{θR}`.

**CT2 (Schur bound + coercivity survival).**  A finite-range operator with
entrywise block bound `β` has operator norm `≤ β·N_R`
(`physicalOpNorm_le_of_kernelBound_finiteRange`, the block Schur test with
ball-cardinality constant `N_R`).  The tilt perturbation `K_θ − K` has
entrywise bound `M(e^{θR} − 1)` (two-sided, via `e^s + e^{−s} ≥ 2`), hence
`‖K_θ − K‖ ≤ M(e^{θR}−1)N_R`, hence coercivity survives:
`IsCoerciveCLM K c → IsCoerciveCLM K_θ (c − M(e^{θR}−1)N_R)`
(`isCoerciveCLM_physicalTiltConj`).

**Honest scope.**  CT1+CT2 only.  The tilted inverse (CT3), the kernel
extraction `|K⁻¹(x,y)| ≤ (2/c)e^{−θ d(x,y)}` and its instantiation on the
flat physical shell (CT4) are the next bricks; the constants here are
fixed-volume (`N_R`, and eventually `c` from the fixed-volume
block-Poincaré), and the volume-uniformity guard of §3ter applies.  Nothing
here touches the interacting integral (G5).

**Source.**  Combes–Thomas (CMP 34, 1973) finite-dimensional weighted
conjugation; Bałaban propagator bounds (CMP 95/99) as the target application;
strategy/framing Lluis Eriksson.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

variable {d N Nc : ℕ} [NeZero N]

/-! ## CT1 — the exponential tilt -/

/-- **CT1 tilt operator**: multiplication by `e^{θ·dist r q}` at bond `q`,
as a continuous linear map on physical one-cochains. -/
noncomputable def physicalTiltCLM
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (r : PhysicalBond d N) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 fun q => Real.exp (θ * (dist r q : ℝ)) • f q
      map_add' := fun f g => by
        apply PiLp.ext
        intro q
        exact smul_add (Real.exp (θ * (dist r q : ℝ))) (f q) (g q)
      map_smul' := fun c f => by
        apply PiLp.ext
        intro q
        exact smul_comm (Real.exp (θ * (dist r q : ℝ))) c (f q) }

@[simp]
theorem physicalTiltCLM_apply
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (r q : PhysicalBond d N)
    (f : PhysicalGaugeOneCochain d N Nc) :
    physicalTiltCLM (Nc := Nc) dist θ r f q =
      Real.exp (θ * (dist r q : ℝ)) • f q := rfl

/-- Tilts compose additively in the rate. -/
theorem physicalTiltCLM_comp
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ₁ θ₂ : ℝ)
    (r : PhysicalBond d N) :
    (physicalTiltCLM (Nc := Nc) dist θ₁ r).comp
        (physicalTiltCLM (Nc := Nc) dist θ₂ r) =
      physicalTiltCLM (Nc := Nc) dist (θ₁ + θ₂) r := by
  refine ContinuousLinearMap.ext fun f => ?_
  apply PiLp.ext
  intro q
  simp only [ContinuousLinearMap.comp_apply, physicalTiltCLM_apply, smul_smul,
    ← Real.exp_add, add_mul]

/-- The zero tilt is the identity. -/
theorem physicalTiltCLM_zero
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (r : PhysicalBond d N) :
    physicalTiltCLM (Nc := Nc) dist 0 r =
      ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc) := by
  refine ContinuousLinearMap.ext fun f => ?_
  apply PiLp.ext
  intro q
  simp [physicalTiltCLM_apply]

/-- The tilt at `−θ` is a right inverse of the tilt at `θ`. -/
theorem physicalTiltCLM_comp_neg
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (r : PhysicalBond d N) :
    (physicalTiltCLM (Nc := Nc) dist θ r).comp
        (physicalTiltCLM (Nc := Nc) dist (-θ) r) =
      ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc) := by
  rw [physicalTiltCLM_comp]
  simpa using physicalTiltCLM_zero (Nc := Nc) dist r

/-- The tilt at `θ` is a right inverse of the tilt at `−θ`. -/
theorem physicalTiltCLM_neg_comp
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (r : PhysicalBond d N) :
    (physicalTiltCLM (Nc := Nc) dist (-θ) r).comp
        (physicalTiltCLM (Nc := Nc) dist θ r) =
      ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc) := by
  rw [physicalTiltCLM_comp]
  simpa using physicalTiltCLM_zero (Nc := Nc) dist r

/-- **CT1 conjugated operator** `K_θ = T_θ ∘ K ∘ T_{−θ}`. -/
noncomputable def physicalTiltConjCLM
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (r : PhysicalBond d N)
    (K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc :=
  (physicalTiltCLM (Nc := Nc) dist θ r).comp
    (K.comp (physicalTiltCLM (Nc := Nc) dist (-θ) r))

/-- The conjugation identity in the direction consumed by kernel extraction:
`K = T_{−θ} ∘ K_θ ∘ T_θ`. -/
theorem physicalTiltConjCLM_conj_identity
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (r : PhysicalBond d N)
    (K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc) :
    (physicalTiltCLM (Nc := Nc) dist (-θ) r).comp
        ((physicalTiltConjCLM (Nc := Nc) dist θ r K).comp
          (physicalTiltCLM (Nc := Nc) dist θ r)) = K := by
  unfold physicalTiltConjCLM
  rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc,
    physicalTiltCLM_neg_comp, ContinuousLinearMap.comp_id,
    ← ContinuousLinearMap.comp_assoc, physicalTiltCLM_neg_comp,
    ContinuousLinearMap.id_comp]

/-- **CT1 entry identity**: conjugation multiplies the kernel entry
`(q, p)` by `e^{θ(dist r q − dist r p)}`. -/
theorem physicalTiltConjCLM_single_apply
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (r p q : PhysicalBond d N) (v : SUNLieCoord Nc)
    (K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc) :
    physicalTiltConjCLM (Nc := Nc) dist θ r K
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q =
      Real.exp (θ * ((dist r q : ℝ) - (dist r p : ℝ))) •
        K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q := by
  have hsingle : physicalTiltCLM (Nc := Nc) dist (-θ) r
      (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) =
      Real.exp (-θ * (dist r p : ℝ)) •
        singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v := by
    apply PiLp.ext
    intro q'
    by_cases hq'p : q' = p
    · subst hq'p
      simp [physicalTiltCLM_apply, PiLp.smul_apply]
    · simp [physicalTiltCLM_apply, PiLp.smul_apply,
        singlePhysicalBondCochain_of_ne (v := v) hq'p]
  unfold physicalTiltConjCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hsingle,
    map_smul, map_smul]
  have happ : (physicalTiltCLM (Nc := Nc) dist θ r
      (K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))) q =
      Real.exp (θ * (dist r q : ℝ)) •
        K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q :=
    physicalTiltCLM_apply dist θ r q _
  calc (Real.exp (-θ * (dist r p : ℝ)) •
        physicalTiltCLM (Nc := Nc) dist θ r
          (K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))) q
      = Real.exp (-θ * (dist r p : ℝ)) •
          (physicalTiltCLM (Nc := Nc) dist θ r
            (K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))) q := rfl
    _ = Real.exp (-θ * (dist r p : ℝ)) •
          (Real.exp (θ * (dist r q : ℝ)) •
            K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q) := by
        rw [happ]
    _ = Real.exp (θ * ((dist r q : ℝ) - (dist r p : ℝ))) •
          K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q := by
        rw [smul_smul, ← Real.exp_add]
        congr 2
        ring

/-- **CT1 range preservation**: conjugation does not change the kernel
support. -/
theorem physicalTiltConjCLM_finiteRange
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (r : PhysicalBond d N) {R : ℕ}
    {K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hK : PhysicalCovarianceFiniteRange K dist R) :
    PhysicalCovarianceFiniteRange
      (physicalTiltConjCLM (Nc := Nc) dist θ r K) dist R := by
  intro p q v hR
  rw [physicalTiltConjCLM_single_apply, hK p q v hR, smul_zero]

/-- For a symmetric triangle distance, `|dist r q − dist r p| ≤ dist q p`. -/
theorem abs_dist_sub_le_of_symm_triangle
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (r p q : PhysicalBond d N) :
    |(dist r q : ℝ) - (dist r p : ℝ)| ≤ (dist q p : ℝ) := by
  rw [abs_sub_le_iff]
  constructor
  · have h : dist r q ≤ dist r p + dist q p := by
      calc dist r q ≤ dist r p + dist p q := htri r p q
        _ = dist r p + dist q p := by rw [hsymm p q]
    have hR : (dist r q : ℝ) ≤ (dist r p : ℝ) + (dist q p : ℝ) := by
      exact_mod_cast h
    linarith
  · have h : dist r p ≤ dist r q + dist q p := htri r q p
    have hR : (dist r p : ℝ) ≤ (dist r q : ℝ) + (dist q p : ℝ) := by
      exact_mod_cast h
    linarith

/-- **CT1 tilted entry bound**: the conjugated kernel keeps range `R` and its
entrywise bound degrades by at most `e^{θR}`. -/
theorem physicalTiltConjCLM_kernelBound
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    {θ : ℝ} (hθ : 0 ≤ θ) (r : PhysicalBond d N) {R : ℕ} {M : ℝ} (hM : 0 ≤ M)
    {K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M)) :
    PhysicalCovarianceKernelBound
      (physicalTiltConjCLM (Nc := Nc) dist θ r K)
      (fun _ _ => M * Real.exp (θ * (R : ℝ))) := by
  intro p q v
  by_cases hR : R < dist q p
  · rw [physicalTiltConjCLM_single_apply, hrange p q v hR, smul_zero]
    have hpos : (0:ℝ) ≤ M * Real.exp (θ * (R : ℝ)) * ‖v‖ := by positivity
    simpa using hpos
  · push_neg at hR
    rw [physicalTiltConjCLM_single_apply, norm_smul, Real.norm_eq_abs,
      Real.abs_exp]
    have habs : |(dist r q : ℝ) - (dist r p : ℝ)| ≤ (dist q p : ℝ) :=
      abs_dist_sub_le_of_symm_triangle dist hsymm htri r p q
    have hfac : Real.exp (θ * ((dist r q : ℝ) - (dist r p : ℝ)))
        ≤ Real.exp (θ * (R : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have h1 : (dist r q : ℝ) - (dist r p : ℝ) ≤ (dist q p : ℝ) :=
        le_of_abs_le habs
      have h2 : (dist q p : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      calc θ * ((dist r q : ℝ) - (dist r p : ℝ))
          ≤ θ * (dist q p : ℝ) := mul_le_mul_of_nonneg_left h1 hθ
        _ ≤ θ * (R : ℝ) := mul_le_mul_of_nonneg_left h2 hθ
    have hKb := hbound p q v
    calc Real.exp (θ * ((dist r q : ℝ) - (dist r p : ℝ))) *
          ‖K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q‖
        ≤ Real.exp (θ * (R : ℝ)) * (M * ‖v‖) :=
          mul_le_mul hfac hKb (norm_nonneg _) (Real.exp_pos _).le
      _ = M * Real.exp (θ * (R : ℝ)) * ‖v‖ := by ring

/-! ## CT2 — block Schur bound and coercivity survival -/

/-- Sums of cochains evaluate pointwise. -/
theorem physicalCochain_sum_apply {ι : Type*} (s : Finset ι)
    (g : ι → PhysicalGaugeOneCochain d N Nc) (q : PhysicalBond d N) :
    (∑ i ∈ s, g i) q = ∑ i ∈ s, g i q := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    rfl

/-- Every physical one-cochain is the sum of its single-bond probes. -/
theorem sum_singlePhysicalBondCochain_eq
    (f : PhysicalGaugeOneCochain d N Nc) :
    ∑ p, singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p (f p) = f := by
  classical
  apply PiLp.ext
  intro q
  rw [physicalCochain_sum_apply]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hpq
    exact singlePhysicalBondCochain_of_ne (f p) (Ne.symm hpq)
  · intro hq
    exact absurd (Finset.mem_univ q) hq

/-- **CT2 block Schur bound**: a finite-range operator with entrywise block
bound `β` has operator norm at most `β·N_R`, where `N_R` bounds the ball
cardinalities of the (symmetric) distance. -/
theorem physicalOpNorm_le_of_kernelBound_finiteRange
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    {R NR : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {A : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hrange : PhysicalCovarianceFiniteRange A dist R)
    (hentry : PhysicalCovarianceKernelBound A (fun _ _ => β)) :
    ‖A‖ ≤ β * (NR : ℝ) := by
  classical
  have hβNR : (0:ℝ) ≤ β * (NR : ℝ) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hβNR
  intro f
  have hdecomp : A f = ∑ p, A (singlePhysicalBondCochain
      (d := d) (N := N) (Nc := Nc) p (f p)) := by
    rw [← map_sum, sum_singlePhysicalBondCochain_eq]
  -- pointwise bound
  have hpoint : ∀ q : PhysicalBond d N,
      ‖A f q‖ ≤ β * ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ := by
    intro q
    have happ : A f q = ∑ p, A (singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) p (f p)) q := by
      rw [hdecomp, physicalCochain_sum_apply]
    have hsplit : ∑ p, A (singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) p (f p)) q
      = ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R),
          A (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p (f p)) q := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro p _ hne
      by_contra hgt
      push_neg at hgt
      exact hne (hrange p q (f p) hgt)
    rw [happ, hsplit]
    calc ‖∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R),
          A (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p (f p)) q‖
        ≤ ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R),
            ‖A (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p (f p)) q‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), β * ‖f p‖ :=
          Finset.sum_le_sum (fun p _ => hentry p q (f p))
      _ = β * ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ := by
          rw [Finset.mul_sum]
  -- square, Cauchy–Schwarz, double count
  have hsq : ‖A f‖ ^ 2 ≤ (β * (NR : ℝ) * ‖f‖) ^ 2 := by
    have hAf : ‖A f‖ ^ 2 = ∑ q, ‖A f q‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ (A f)
    have hff : ‖f‖ ^ 2 = ∑ p, ‖f p‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ f
    have hterm : ∀ q, ‖A f q‖ ^ 2 ≤
        β ^ 2 * (NR : ℝ) *
          ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2 := by
      intro q
      have h1 : ‖A f q‖ ^ 2 ≤
          (β * ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hpoint q) 2
      have hCS : (∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖) ^ 2
          ≤ ((Finset.univ.filter (fun p => dist q p ≤ R)).card : ℝ) *
            ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      have hcard : ((Finset.univ.filter (fun p => dist q p ≤ R)).card : ℝ)
          ≤ (NR : ℝ) := by exact_mod_cast hNR q
      have hsum_nonneg : (0:ℝ) ≤
          ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2 :=
        Finset.sum_nonneg (fun p _ => sq_nonneg _)
      calc ‖A f q‖ ^ 2
          ≤ (β * ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖) ^ 2 := h1
        _ = β ^ 2 * (∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖) ^ 2 := by
            ring
        _ ≤ β ^ 2 * (((Finset.univ.filter (fun p => dist q p ≤ R)).card : ℝ) *
              ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hCS (sq_nonneg β)
        _ ≤ β ^ 2 * ((NR : ℝ) *
              ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hcard hsum_nonneg) (sq_nonneg β)
        _ = β ^ 2 * (NR : ℝ) *
              ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2 := by
            ring
    have hswap : ∑ q, ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2
        = ∑ p, ((Finset.univ.filter (fun q => dist q p ≤ R)).card : ℝ) * ‖f p‖ ^ 2 := by
      have h1 : ∀ q : PhysicalBond d N,
          ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2
          = ∑ p, if dist q p ≤ R then ‖f p‖ ^ 2 else 0 :=
        fun q => Finset.sum_filter _ _
      have h2 : ∀ p : PhysicalBond d N,
          ∑ q, (if dist q p ≤ R then ‖f p‖ ^ 2 else 0)
          = ((Finset.univ.filter (fun q => dist q p ≤ R)).card : ℝ) * ‖f p‖ ^ 2 := by
        intro p
        calc ∑ q, (if dist q p ≤ R then ‖f p‖ ^ 2 else 0)
            = ∑ q ∈ Finset.univ.filter (fun q => dist q p ≤ R), ‖f p‖ ^ 2 :=
              (Finset.sum_filter _ _).symm
          _ = ((Finset.univ.filter (fun q => dist q p ≤ R)).card : ℝ) * ‖f p‖ ^ 2 := by
              rw [Finset.sum_const, nsmul_eq_mul]
      calc ∑ q, ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2
          = ∑ q, ∑ p, if dist q p ≤ R then ‖f p‖ ^ 2 else 0 := by
            exact Finset.sum_congr rfl (fun q _ => h1 q)
        _ = ∑ p, ∑ q, if dist q p ≤ R then ‖f p‖ ^ 2 else 0 := Finset.sum_comm
        _ = ∑ p, ((Finset.univ.filter (fun q => dist q p ≤ R)).card : ℝ) * ‖f p‖ ^ 2 :=
            Finset.sum_congr rfl (fun p _ => h2 p)
    have htrans : ∀ p : PhysicalBond d N,
        ((Finset.univ.filter (fun q => dist q p ≤ R)).card : ℝ) ≤ (NR : ℝ) := by
      intro p
      have hfe : Finset.univ.filter (fun q => dist q p ≤ R)
          = Finset.univ.filter (fun q => dist p q ≤ R) := by
        apply Finset.filter_congr
        intro x _
        rw [hsymm x p]
      rw [hfe]
      exact_mod_cast hNR p
    have hdouble : ∑ q, ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2
        ≤ (NR : ℝ) * ∑ p, ‖f p‖ ^ 2 := by
      rw [hswap, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (htrans p) (sq_nonneg _)
    calc ‖A f‖ ^ 2 = ∑ q, ‖A f q‖ ^ 2 := hAf
      _ ≤ ∑ q, β ^ 2 * (NR : ℝ) *
            ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2 :=
          Finset.sum_le_sum (fun q _ => hterm q)
      _ = β ^ 2 * (NR : ℝ) *
            ∑ q, ∑ p ∈ Finset.univ.filter (fun p => dist q p ≤ R), ‖f p‖ ^ 2 := by
          rw [← Finset.mul_sum]
      _ ≤ β ^ 2 * (NR : ℝ) * ((NR : ℝ) * ∑ p, ‖f p‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left hdouble
          positivity
      _ = (β * (NR : ℝ) * ‖f‖) ^ 2 := by
          rw [← hff]
          ring
  have h1 : (0:ℝ) ≤ ‖A f‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ β * (NR : ℝ) * ‖f‖ := by positivity
  have hs := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at hs

/-- Two-sided tilt-factor estimate: `|e^t − 1| ≤ e^s − 1` for `|t| ≤ s`
(the lower side uses `e^s + e^{−s} ≥ 2`). -/
theorem abs_exp_sub_one_le_of_abs_le {t s : ℝ} (ht : |t| ≤ s) :
    |Real.exp t - 1| ≤ Real.exp s - 1 := by
  rw [abs_le] at ht
  rw [abs_le]
  constructor
  · have h1 : Real.exp (-s) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
    have h2 : (2:ℝ) ≤ Real.exp s + Real.exp (-s) := by
      have hmul : Real.exp s * Real.exp (-s) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [sq_nonneg (Real.exp s - 1), Real.exp_pos s]
    linarith
  · have h1 : Real.exp t ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith)
    linarith

/-- **CT2 perturbation entry bound**: the tilt perturbation `K_θ − K` has
kernel entries bounded by `M(e^{θR} − 1)` and keeps range `R`. -/
theorem physicalTiltConj_sub_kernelBound
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    {θ : ℝ} (hθ : 0 ≤ θ) (r : PhysicalBond d N) {R : ℕ} {M : ℝ} (hM : 0 ≤ M)
    {K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M)) :
    PhysicalCovarianceKernelBound
      (physicalTiltConjCLM (Nc := Nc) dist θ r K - K)
      (fun _ _ => M * (Real.exp (θ * (R : ℝ)) - 1)) := by
  intro p q v
  have hexpR : (1:ℝ) ≤ Real.exp (θ * (R : ℝ)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have happ : (physicalTiltConjCLM (Nc := Nc) dist θ r K - K)
      (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q =
      (Real.exp (θ * ((dist r q : ℝ) - (dist r p : ℝ))) - 1) •
        K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q := by
    rw [ContinuousLinearMap.sub_apply]
    have hsub : (physicalTiltConjCLM (Nc := Nc) dist θ r K
          (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v)
        - K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v)) q
      = physicalTiltConjCLM (Nc := Nc) dist θ r K
          (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q
        - K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q := rfl
    rw [hsub, physicalTiltConjCLM_single_apply, sub_smul, one_smul]
  by_cases hR : R < dist q p
  · rw [happ, hrange p q v hR, smul_zero]
    have hpos : (0:ℝ) ≤ M * (Real.exp (θ * (R : ℝ)) - 1) * ‖v‖ := by
      have : (0:ℝ) ≤ Real.exp (θ * (R : ℝ)) - 1 := by linarith
      positivity
    simpa using hpos
  · push_neg at hR
    rw [happ, norm_smul, Real.norm_eq_abs]
    have habs : |(dist r q : ℝ) - (dist r p : ℝ)| ≤ (dist q p : ℝ) :=
      abs_dist_sub_le_of_symm_triangle dist hsymm htri r p q
    have hRr : (dist q p : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have htilt : |θ * ((dist r q : ℝ) - (dist r p : ℝ))| ≤ θ * (R : ℝ) := by
      rw [abs_mul, abs_of_nonneg hθ]
      apply mul_le_mul_of_nonneg_left _ hθ
      exact le_trans habs hRr
    have hfac : |Real.exp (θ * ((dist r q : ℝ) - (dist r p : ℝ))) - 1|
        ≤ Real.exp (θ * (R : ℝ)) - 1 :=
      abs_exp_sub_one_le_of_abs_le htilt
    have hKb := hbound p q v
    calc |Real.exp (θ * ((dist r q : ℝ) - (dist r p : ℝ))) - 1| *
          ‖K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q‖
        ≤ (Real.exp (θ * (R : ℝ)) - 1) * (M * ‖v‖) := by
          apply mul_le_mul hfac hKb (norm_nonneg _) (by linarith)
      _ = M * (Real.exp (θ * (R : ℝ)) - 1) * ‖v‖ := by ring

/-- The tilt perturbation keeps the kernel range. -/
theorem physicalTiltConj_sub_finiteRange
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (θ : ℝ)
    (r : PhysicalBond d N) {R : ℕ}
    {K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hrange : PhysicalCovarianceFiniteRange K dist R) :
    PhysicalCovarianceFiniteRange
      (physicalTiltConjCLM (Nc := Nc) dist θ r K - K) dist R := by
  intro p q v hR
  have hzero := hrange p q v hR
  have hconj := physicalTiltConjCLM_finiteRange (Nc := Nc) dist θ r hrange p q v hR
  have hsub : (physicalTiltConjCLM (Nc := Nc) dist θ r K - K)
      (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q =
      physicalTiltConjCLM (Nc := Nc) dist θ r K
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q -
      K (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q := rfl
  rw [hsub, hzero, hconj, sub_zero]

/-- **CT2 perturbation operator-norm bound**:
`‖K_θ − K‖ ≤ M(e^{θR} − 1)·N_R`. -/
theorem norm_physicalTiltConj_sub_le
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    {θ : ℝ} (hθ : 0 ≤ θ) (r : PhysicalBond d N) {R NR : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M)) :
    ‖physicalTiltConjCLM (Nc := Nc) dist θ r K - K‖
      ≤ M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) := by
  have hexpR : (1:ℝ) ≤ Real.exp (θ * (R : ℝ)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hβ : (0:ℝ) ≤ M * (Real.exp (θ * (R : ℝ)) - 1) := by
    have : (0:ℝ) ≤ Real.exp (θ * (R : ℝ)) - 1 := by linarith
    positivity
  exact physicalOpNorm_le_of_kernelBound_finiteRange dist hsymm hβ hNR
    (physicalTiltConj_sub_finiteRange dist θ r hrange)
    (physicalTiltConj_sub_kernelBound dist hsymm htri hθ r hM hrange hbound)

/-- **CT2 capstone — coercivity survives the tilt**: if `K` is coercive with
constant `c`, then the conjugated operator `K_θ` is coercive with constant
`c − M(e^{θR} − 1)·N_R`.  This is the analytic heart of the coercive
Combes–Thomas route: the θ-budget `M(e^{θR}−1)N_R ≤ c/2` (to be instantiated
in CT3/CT4) keeps the tilted operator invertible with a volume-explicit
bound. -/
theorem isCoerciveCLM_physicalTiltConj
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    {θ : ℝ} (hθ : 0 ≤ θ) (r : PhysicalBond d N) {R NR : ℕ} {M c : ℝ} (hM : 0 ≤ M)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {K : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hc : IsCoerciveCLM K c) :
    IsCoerciveCLM (physicalTiltConjCLM (Nc := Nc) dist θ r K)
      (c - M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ)) := by
  have hsplit : physicalTiltConjCLM (Nc := Nc) dist θ r K =
      K + (physicalTiltConjCLM (Nc := Nc) dist θ r K - K) := by
    abel
  rw [hsplit]
  exact isCoercive_add_of_opNorm_le K _ hc
    (norm_physicalTiltConj_sub_le dist hsymm htri hθ r hM hNR hrange hbound)

end YangMills.RG
