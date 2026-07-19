/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCoerciveCombesThomasInverse

/-!
# Tilted second resolvent identity on physical gauge cochains

This module isolates the exact operator algebra needed to compare two physical
covariances.  If `C₀` and `C₁` invert precisions `K₀` and `K₁`, then

`C₁ - C₀ = C₁ ∘ (K₀ - K₁) ∘ C₀`.

The identity is transported through the Combes--Thomas tilt.  Coercivity of
the two tilted precisions and a norm bound for the tilted precision defect then
give an exponentially decaying kernel bound for `C₁ - C₀`.

Honest scope: this is a physical covariance-correction theorem.  It does not
identify the correction with any of the CMP116 kernels `R₁`, `R₂`, or `R₃`;
that identification still requires the source-specific random-walk
decomposition.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero N]

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc

/-- Conjugation by the physical exponential tilt preserves addition. -/
theorem physicalTiltConjCLM_add
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (θ : ℝ) (root : PhysicalBond d N)
    (A B : PhysicalEndomorphism d N Nc) :
    physicalTiltConjCLM (Nc := Nc) dist θ root (A + B) =
      physicalTiltConjCLM (Nc := Nc) dist θ root A +
        physicalTiltConjCLM (Nc := Nc) dist θ root B := by
  apply ContinuousLinearMap.ext
  intro x
  unfold physicalTiltConjCLM
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add]

/-- Conjugation by the physical exponential tilt preserves subtraction. -/
theorem physicalTiltConjCLM_sub
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (θ : ℝ) (root : PhysicalBond d N)
    (A B : PhysicalEndomorphism d N Nc) :
    physicalTiltConjCLM (Nc := Nc) dist θ root (A - B) =
      physicalTiltConjCLM (Nc := Nc) dist θ root A -
        physicalTiltConjCLM (Nc := Nc) dist θ root B := by
  apply ContinuousLinearMap.ext
  intro x
  unfold physicalTiltConjCLM
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    map_sub]

/-- Conjugation by the physical exponential tilt preserves composition. -/
theorem physicalTiltConjCLM_comp
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (θ : ℝ) (root : PhysicalBond d N)
    (A B : PhysicalEndomorphism d N Nc) :
    physicalTiltConjCLM (Nc := Nc) dist θ root (A.comp B) =
      (physicalTiltConjCLM (Nc := Nc) dist θ root A).comp
        (physicalTiltConjCLM (Nc := Nc) dist θ root B) := by
  apply ContinuousLinearMap.ext
  intro x
  unfold physicalTiltConjCLM
  simp only [ContinuousLinearMap.comp_apply]
  have hinv :
      physicalTiltCLM (Nc := Nc) dist (-θ) root
          (physicalTiltCLM (Nc := Nc) dist θ root
            (B (physicalTiltCLM (Nc := Nc) dist (-θ) root x))) =
        B (physicalTiltCLM (Nc := Nc) dist (-θ) root x) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg
        (fun f => f (B (physicalTiltCLM (Nc := Nc) dist (-θ) root x)))
        (physicalTiltCLM_neg_comp (Nc := Nc) dist θ root)
  rw [hinv]

/-- Exact second resolvent identity.  Only the two inverse orientations used
by the displayed factorization are assumed. -/
theorem covariance_sub_eq_comp_precision_sub_comp
    (K₀ K₁ C₀ C₁ : PhysicalEndomorphism d N Nc)
    (hC₁K₁ :
      C₁.comp K₁ =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc))
    (hK₀C₀ :
      K₀.comp C₀ =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc)) :
    C₁ - C₀ = C₁.comp ((K₀ - K₁).comp C₀) := by
  apply ContinuousLinearMap.ext
  intro x
  have hright :
      K₀ (C₀ x) = x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun f => f x) hK₀C₀
  have hleft :
      C₁ (K₁ (C₀ x)) = C₀ x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun f => f (C₀ x)) hC₁K₁
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, hright, hleft]

/-- A supplied right inverse of a coercive operator has norm at most the
inverse coercivity constant. -/
theorem norm_rightInverse_le_of_isCoerciveCLM
    (K C : PhysicalEndomorphism d N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hKC :
      K.comp C =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc)) :
    ‖C‖ ≤ c⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound C (inv_nonneg.mpr hc.le) ?_
  intro y
  have hlower := isCoerciveCLM_norm_lower_bound K hcoer (C y)
  have hKy : K (C y) = y := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun f => f y) hKC
  rw [hKy] at hlower
  have hdiv : ‖C y‖ ≤ ‖y‖ / c := (le_div_iff₀ hc).2 (by
    simpa [mul_comm] using hlower)
  simpa [div_eq_mul_inv, mul_comm] using hdiv

/-- The conjugated covariance is a right inverse of the conjugated precision. -/
theorem physicalTiltConjCLM_precision_comp_covariance
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (θ : ℝ) (root : PhysicalBond d N)
    (K C : PhysicalEndomorphism d N Nc)
    (hKC :
      K.comp C =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc)) :
    (physicalTiltConjCLM (Nc := Nc) dist θ root K).comp
        (physicalTiltConjCLM (Nc := Nc) dist θ root C) =
      ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc) := by
  rw [← physicalTiltConjCLM_comp, hKC]
  unfold physicalTiltConjCLM
  rw [ContinuousLinearMap.id_comp, physicalTiltCLM_comp_neg]

/-- Norm of a conjugated inverse from coercivity of the conjugated precision. -/
theorem norm_physicalTiltConj_covariance_le_of_coercive
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (θ : ℝ) (root : PhysicalBond d N)
    (K C : PhysicalEndomorphism d N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer :
      IsCoerciveCLM
        (physicalTiltConjCLM (Nc := Nc) dist θ root K) c)
    (hKC :
      K.comp C =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc)) :
    ‖physicalTiltConjCLM (Nc := Nc) dist θ root C‖ ≤ c⁻¹ := by
  exact norm_rightInverse_le_of_isCoerciveCLM
    (physicalTiltConjCLM (Nc := Nc) dist θ root K)
    (physicalTiltConjCLM (Nc := Nc) dist θ root C)
    hc hcoer
    (physicalTiltConjCLM_precision_comp_covariance
      dist θ root K C hKC)

/-- Pure norm form of the tilted second resolvent estimate. -/
theorem norm_physicalTiltConj_covariance_sub_le
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (θ : ℝ) (root : PhysicalBond d N)
    (K₀ K₁ C₀ C₁ : PhysicalEndomorphism d N Nc)
    (hC₁K₁ :
      C₁.comp K₁ =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc))
    (hK₀C₀ :
      K₀.comp C₀ =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc))
    {b₀ b₁ defectBound : ℝ}
    (hdefectBound : 0 ≤ defectBound)
    (hC₀ :
      ‖physicalTiltConjCLM (Nc := Nc) dist θ root C₀‖ ≤ b₀)
    (hC₁ :
      ‖physicalTiltConjCLM (Nc := Nc) dist θ root C₁‖ ≤ b₁)
    (hdefect :
      ‖physicalTiltConjCLM (Nc := Nc) dist θ root (K₀ - K₁)‖ ≤
        defectBound) :
    ‖physicalTiltConjCLM (Nc := Nc) dist θ root (C₁ - C₀)‖ ≤
      b₁ * defectBound * b₀ := by
  have hb₀ : 0 ≤ b₀ :=
    le_trans (norm_nonneg
      (physicalTiltConjCLM (Nc := Nc) dist θ root C₀)) hC₀
  have hb₁ : 0 ≤ b₁ :=
    le_trans (norm_nonneg
      (physicalTiltConjCLM (Nc := Nc) dist θ root C₁)) hC₁
  rw [covariance_sub_eq_comp_precision_sub_comp
    K₀ K₁ C₀ C₁ hC₁K₁ hK₀C₀,
    physicalTiltConjCLM_comp, physicalTiltConjCLM_comp]
  calc
    ‖(physicalTiltConjCLM (Nc := Nc) dist θ root C₁).comp
        ((physicalTiltConjCLM (Nc := Nc) dist θ root (K₀ - K₁)).comp
          (physicalTiltConjCLM (Nc := Nc) dist θ root C₀))‖
        ≤ ‖physicalTiltConjCLM (Nc := Nc) dist θ root C₁‖ *
            ‖(physicalTiltConjCLM (Nc := Nc) dist θ root (K₀ - K₁)).comp
              (physicalTiltConjCLM (Nc := Nc) dist θ root C₀)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖physicalTiltConjCLM (Nc := Nc) dist θ root C₁‖ *
          (‖physicalTiltConjCLM (Nc := Nc) dist θ root (K₀ - K₁)‖ *
            ‖physicalTiltConjCLM (Nc := Nc) dist θ root C₀‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ b₁ * (defectBound * b₀) := by
          gcongr
    _ = b₁ * defectBound * b₀ := by ring

/-- A uniform norm bound on every rooted conjugate implies exponential decay
of the original physical kernel. -/
theorem physicalCovarianceExponentialKernelBound_of_tilted_opNorm
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    {θ A : ℝ} (hθ : 0 < θ) (hA : 0 ≤ A)
    (C : PhysicalEndomorphism d N Nc)
    (htilt :
      ∀ root : PhysicalBond d N,
        ‖physicalTiltConjCLM (Nc := Nc) dist θ root C‖ ≤ A) :
    PhysicalCovarianceExponentialKernelBound C dist A θ := by
  refine ⟨hA, hθ, ?_⟩
  intro source target v
  have hroot :
      physicalTiltCLM (Nc := Nc) dist (-θ) source
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v) =
        singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) source v :=
    physicalTiltCLM_single_root dist (-θ) source v (hself source)
  have hconj :
      physicalTiltConjCLM (Nc := Nc) dist θ source C
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v) =
        physicalTiltCLM (Nc := Nc) dist θ source
          (C (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v)) := by
    unfold physicalTiltConjCLM
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hroot]
  have hentry :
      C (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) source v) target =
        Real.exp (-θ * (dist source target : ℝ)) •
          physicalTiltConjCLM (Nc := Nc) dist θ source C
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) source v) target := by
    rw [hconj]
    exact physicalCovariance_entry_untilt dist θ C source target v
  calc
    ‖C (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) source v) target‖
        = Real.exp (-θ * (dist source target : ℝ)) *
            ‖physicalTiltConjCLM (Nc := Nc) dist θ source C
              (singlePhysicalBondCochain
                (d := d) (N := N) (Nc := Nc) source v) target‖ := by
          rw [hentry, norm_smul, Real.norm_eq_abs, Real.abs_exp]
    _ ≤ Real.exp (-θ * (dist source target : ℝ)) *
          ‖physicalTiltConjCLM (Nc := Nc) dist θ source C
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) source v)‖ := by
          gcongr
          exact PiLp.norm_apply_le _ target
    _ ≤ Real.exp (-θ * (dist source target : ℝ)) *
          (A * ‖singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v‖) := by
          gcongr
          exact ContinuousLinearMap.le_of_opNorm_le
            (physicalTiltConjCLM (Nc := Nc) dist θ source C)
            (htilt source) _
    _ = A * Real.exp (-(θ * (dist target source : ℝ))) * ‖v‖ := by
          rw [norm_singlePhysicalBondCochain]
          rw [hsymm source target]
          ring_nf

/-- Tilted second-resolvent endpoint.  Uniform coercivity of the two tilted
precisions and a uniform norm bound for their tilted difference imply
exponential localization of the covariance difference. -/
theorem physicalCovarianceExponentialKernelBound_sub_of_tilted_resolvent
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    {θ c₀ c₁ defectBound : ℝ}
    (hθ : 0 < θ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hdefectBound : 0 ≤ defectBound)
    (K₀ K₁ C₀ C₁ : PhysicalEndomorphism d N Nc)
    (hC₁K₁ :
      C₁.comp K₁ =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc))
    (hK₀C₀ :
      K₀.comp C₀ =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc))
    (hK₁C₁ :
      K₁.comp C₁ =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc))
    (hcoer₀ :
      ∀ root : PhysicalBond d N,
        IsCoerciveCLM
          (physicalTiltConjCLM (Nc := Nc) dist θ root K₀) (c₀ / 2))
    (hcoer₁ :
      ∀ root : PhysicalBond d N,
        IsCoerciveCLM
          (physicalTiltConjCLM (Nc := Nc) dist θ root K₁) (c₁ / 2))
    (hdefect :
      ∀ root : PhysicalBond d N,
        ‖physicalTiltConjCLM (Nc := Nc) dist θ root (K₀ - K₁)‖ ≤
          defectBound) :
    PhysicalCovarianceExponentialKernelBound
      (C₁ - C₀) dist
      ((2 / c₁) * defectBound * (2 / c₀)) θ := by
  have hA :
      0 ≤ (2 / c₁) * defectBound * (2 / c₀) := by
    positivity
  apply physicalCovarianceExponentialKernelBound_of_tilted_opNorm
    dist hsymm hself hθ hA
  intro root
  have hC₀tilt :
      ‖physicalTiltConjCLM (Nc := Nc) dist θ root C₀‖ ≤ 2 / c₀ := by
    have h := norm_physicalTiltConj_covariance_le_of_coercive
      dist θ root K₀ C₀ (half_pos hc₀) (hcoer₀ root) hK₀C₀
    rwa [inv_div] at h
  have hC₁tilt :
      ‖physicalTiltConjCLM (Nc := Nc) dist θ root C₁‖ ≤ 2 / c₁ := by
    have h := norm_physicalTiltConj_covariance_le_of_coercive
      dist θ root K₁ C₁ (half_pos hc₁) (hcoer₁ root) hK₁C₁
    rwa [inv_div] at h
  exact norm_physicalTiltConj_covariance_sub_le
    dist θ root K₀ K₁ C₀ C₁ hC₁K₁ hK₀C₀
    hdefectBound hC₀tilt hC₁tilt (hdefect root)

end

end YangMills.RG
