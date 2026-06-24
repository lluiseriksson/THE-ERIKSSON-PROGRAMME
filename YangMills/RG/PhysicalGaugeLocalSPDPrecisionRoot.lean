/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.LocalSPDPrecision
import YangMills.RG.PhysicalGaugeCovarianceLocalization
import YangMills.RG.CoerciveCovariance

/-!
# Physical local-SPD precision to covariance-root certificate frontier

This module packages the first physical-cochain interface for the local SPD
route:

`precision = scale * (id - normalizedPerturbation)`.

It derives the deterministic spectral sandwich, exact covariance by strict
coercivity, and the named kernel-tail estimates already available in
`LocalSPDPrecision`.  It does **not** identify the precision with the Wilson
Hessian, prove operator-power domination, prove that the canonical covariance
is the Neumann series, construct a continuous-linear-map square root, or prove
covariance/root kernel bounds.  Those remain explicit fields of
`PhysicalLocalSPDPrecisionRootCertificate`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

/-- Physical local-SPD data for a normalized finite-range precision shell.

The fields `operatorRatio` and `resolventData.spatialRatio` are intentionally
separate: the former controls operator-norm convergence, while the latter
controls scalar kernel convolutions. -/
structure PhysicalLocalSPDInverseSqrtData
    {d N Nc : ℕ} [NeZero N]
    (precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℝ) where

  scale : ℝ

  normalizedPerturbation :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc

  kernelMajorant :
    PhysicalBond d N → PhysicalBond d N → ℝ

  operatorRatio : ℝ

  scale_pos : 0 < scale
  operatorRatio_nonneg : 0 ≤ operatorRatio
  operatorRatio_lt_one : operatorRatio < 1

  precision_eq :
    precision =
      scale •
        (ContinuousLinearMap.id ℝ
            (PhysicalGaugeOneCochain d N Nc) -
          normalizedPerturbation)

  normalizedPerturbation_selfAdjoint_form :
    ∀ x y : PhysicalGaugeOneCochain d N Nc,
      inner ℝ x (normalizedPerturbation y) =
        inner ℝ (normalizedPerturbation x) y

  normalizedPerturbation_norm_le :
    ‖normalizedPerturbation‖ ≤ operatorRatio

  kernelMajorant_nonneg :
    ∀ target source, 0 ≤ kernelMajorant target source

  normalizedPerturbation_kernel_bound :
    PhysicalCovarianceKernelBound
      normalizedPerturbation kernelMajorant

  resolventData :
    LocalFiniteRangeResolventData dist kernelMajorant

  dist_self :
    ∀ x, dist x x = 0

  range_nonneg :
    0 ≤ resolventData.R

  decayRate_pos :
    0 < resolventData.kappa - resolventData.sigma

/-- The coercivity constant derived from `scale * (id - K)`. -/
def PhysicalLocalSPDInverseSqrtData.coercivityConstant
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) : ℝ :=
  H.scale * (1 - H.operatorRatio)

/-- The corresponding upper spectral constant. -/
def PhysicalLocalSPDInverseSqrtData.spectralUpperConstant
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) : ℝ :=
  H.scale * (1 + H.operatorRatio)

theorem PhysicalLocalSPDInverseSqrtData.coercivityConstant_pos
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) :
    0 < H.coercivityConstant := by
  unfold PhysicalLocalSPDInverseSqrtData.coercivityConstant
  exact mul_pos H.scale_pos (sub_pos.mpr H.operatorRatio_lt_one)

theorem PhysicalLocalSPDInverseSqrtData.precision_coercive
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) :
    IsCoerciveCLM precision H.coercivityConstant := by
  intro x
  let I :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc :=
    ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc)
  have hKupper :
      inner ℝ x (H.normalizedPerturbation x) ≤
        H.operatorRatio * ‖x‖ ^ 2 :=
    inner_apply_le_of_opNorm_le
      H.normalizedPerturbation H.normalizedPerturbation_norm_le x
  have hsub :
      (1 - H.operatorRatio) * ‖x‖ ^ 2 ≤
        inner ℝ x ((I - H.normalizedPerturbation) x) := by
    calc
      (1 - H.operatorRatio) * ‖x‖ ^ 2
          = inner ℝ x x - H.operatorRatio * ‖x‖ ^ 2 := by
            rw [real_inner_self_eq_norm_sq]
            ring
      _ ≤ inner ℝ x x - inner ℝ x (H.normalizedPerturbation x) :=
          sub_le_sub_left hKupper _
      _ = inner ℝ x ((I - H.normalizedPerturbation) x) := by
          simp [I, inner_sub_right]
  calc
    H.coercivityConstant * ‖x‖ ^ 2
        = H.scale * ((1 - H.operatorRatio) * ‖x‖ ^ 2) := by
          unfold PhysicalLocalSPDInverseSqrtData.coercivityConstant
          ring
    _ ≤ H.scale * inner ℝ x ((I - H.normalizedPerturbation) x) :=
        mul_le_mul_of_nonneg_left hsub H.scale_pos.le
    _ = inner ℝ x (precision x) := by
        simp [H.precision_eq, I, inner_smul_right]

theorem PhysicalLocalSPDInverseSqrtData.precision_spectral_upper
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) :
    ∀ x,
      inner ℝ x (precision x) ≤
        H.spectralUpperConstant * ‖x‖ ^ 2 := by
  intro x
  let I :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc :=
    ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc)
  have hKlower :
      -H.operatorRatio * ‖x‖ ^ 2 ≤
        inner ℝ x (H.normalizedPerturbation x) :=
    neg_opNorm_budget_mul_norm_sq_le_inner_apply
      H.normalizedPerturbation H.normalizedPerturbation_norm_le x
  have hsub :
      inner ℝ x ((I - H.normalizedPerturbation) x) ≤
        (1 + H.operatorRatio) * ‖x‖ ^ 2 := by
    have hinner :
        inner ℝ x ((I - H.normalizedPerturbation) x) =
          inner ℝ x x - inner ℝ x (H.normalizedPerturbation x) := by
      simp [I, inner_sub_right]
    rw [hinner, real_inner_self_eq_norm_sq]
    nlinarith [hKlower]
  calc
    inner ℝ x (precision x)
        = H.scale * inner ℝ x ((I - H.normalizedPerturbation) x) := by
          simp [H.precision_eq, I, inner_smul_right]
    _ ≤ H.scale * ((1 + H.operatorRatio) * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsub H.scale_pos.le
    _ = H.spectralUpperConstant * ‖x‖ ^ 2 := by
        unfold PhysicalLocalSPDInverseSqrtData.spectralUpperConstant
        ring

theorem PhysicalLocalSPDInverseSqrtData.precision_selfAdjoint_form
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) :
    ∀ x y,
      inner ℝ x (precision y) =
        inner ℝ (precision x) y := by
  intro x y
  let I :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc :=
    ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc)
  calc
    inner ℝ x (precision y)
        = H.scale *
            inner ℝ x ((I - H.normalizedPerturbation) y) := by
          simp [H.precision_eq, I, inner_smul_right]
    _ = H.scale *
          (inner ℝ x y -
            inner ℝ x (H.normalizedPerturbation y)) := by
        simp [I, inner_sub_right]
    _ = H.scale *
          (inner ℝ x y -
            inner ℝ (H.normalizedPerturbation x) y) := by
        rw [H.normalizedPerturbation_selfAdjoint_form x y]
    _ = H.scale *
          inner ℝ ((I - H.normalizedPerturbation) x) y := by
        simp [I, inner_sub_left]
    _ = inner ℝ (precision x) y := by
        simp [H.precision_eq, I, inner_smul_left]

/-- Exact finite range of the normalized perturbation, as a consequence of the
single-bond kernel bound and the scalar finite-range majorant. -/
theorem PhysicalLocalSPDInverseSqrtData.normalizedPerturbation_finiteRange
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) :
    ∀ source target (v : SUNLieCoord Nc),
      H.resolventData.R < dist target source →
        H.normalizedPerturbation
            (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc)
              source v) target = 0 := by
  intro source target v hfar
  have hmajorant :
      H.kernelMajorant target source = 0 :=
    H.resolventData.finiteRange target source hfar
  have hbound :=
    H.normalizedPerturbation_kernel_bound source target v
  rw [hmajorant, zero_mul] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

/-- The physical precision is finite-range off the diagonal.  The only extra
term relative to the normalized perturbation is the identity contribution, and
the hypotheses `dist_self` and `range_nonneg` rule out that diagonal under
`R < dist target source`. -/
theorem PhysicalLocalSPDInverseSqrtData.precision_finiteRange_offDiagonal
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) :
    ∀ source target (v : SUNLieCoord Nc),
      H.resolventData.R < dist target source →
        precision
            (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc)
              source v) target = 0 := by
  intro source target v hfar
  have hne : target ≠ source := by
    intro hts
    have hdist : dist target source = 0 := by
      simpa [hts] using H.dist_self source
    have hRlt0 : H.resolventData.R < 0 := by
      simpa [hdist] using hfar
    exact (not_lt_of_ge H.range_nonneg) hRlt0
  have hsingle :
      singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) source v target =
        0 :=
    singlePhysicalBondCochain_of_ne
      (d := d) (N := N) (Nc := Nc) (p := source) (q := target) v hne
  have hK :
      H.normalizedPerturbation
          (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc)
            source v) target = 0 :=
    H.normalizedPerturbation_finiteRange source target v hfar
  rw [H.precision_eq]
  simp [hsingle, hK]

theorem PhysicalLocalSPDInverseSqrtData.resolvent_expDecay
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) :
    ExpDecay dist
      H.resolventData.resolventAmplitude
      (H.resolventData.kappa - H.resolventData.sigma)
      (neumannResolventKernel H.kernelMajorant) :=
  H.resolventData.resolvent_expDecay

theorem PhysicalLocalSPDInverseSqrtData.inverseSqrtCoefficient_tail_le
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist)
    (Ntail : ℕ) :
    (∑' n,
      inverseSqrtBinomialCoeff (n + Ntail) *
        H.operatorRatio ^ (n + Ntail)) ≤
      H.operatorRatio ^ Ntail *
        (1 - H.operatorRatio)⁻¹ :=
  inverseSqrtBinomialCoeff_tail_le
    H.operatorRatio_nonneg H.operatorRatio_lt_one Ntail

theorem PhysicalLocalSPDInverseSqrtData.inverseSqrtKernelRemainder_expDecay
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist)
    (Ntail : ℕ) :
    ExpDecay dist
      (H.resolventData.baseAmplitude *
        H.resolventData.spatialRatio ^ Ntail *
        (1 - H.resolventData.spatialRatio)⁻¹)
      (H.resolventData.kappa - H.resolventData.sigma)
      (inverseSqrtKernelRemainder H.kernelMajorant Ntail) :=
  H.resolventData.inverseSqrtKernelRemainder_expDecay Ntail

/-- Scalar finite-range support for the majorant composition powers carried by
physical local-SPD data.  With the convention `Kpow K 0 = K`, the `n`th power
has radius `(n + 1) * R`. -/
theorem PhysicalLocalSPDInverseSqrtData.kernelMajorant_Kpow_finiteRange
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) (n : ℕ) :
    ∀ source target,
      (((n + 1 : ℕ) : ℝ) * H.resolventData.R) < dist target source →
        Kpow H.kernelMajorant n target source = 0 := by
  intro source target hfar
  exact H.resolventData.Kpow_finiteRange n target source hfar

/-- The finite inverse-square-root truncation of the scalar majorant has exact
range `Ntrunc * R`.  This is a scalar support statement only; it does not
construct or identify the physical covariance root. -/
theorem PhysicalLocalSPDInverseSqrtData.inverseSqrtKernelTruncation_finiteRange
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) (Ntrunc : ℕ) :
    ∀ source target,
      (((Ntrunc : ℕ) : ℝ) * H.resolventData.R) < dist target source →
        inverseSqrtKernelTruncation H.kernelMajorant Ntrunc target source = 0 := by
  intro source target hfar
  exact
    H.resolventData.inverseSqrtKernelTruncation_finiteRange
      H.range_nonneg Ntrunc target source hfar

/-- The canonical covariance obtained from strict coercivity of the physical
local-SPD precision. -/
noncomputable def PhysicalLocalSPDInverseSqrtData.covariance
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  covarianceOfIsCoerciveCLM
    precision
    H.coercivityConstant_pos
    H.precision_coercive

/-- Candidate covariance weight for the identity plus Neumann-tail picture.

This is only a weight expression.  The kernel bound for the canonical
covariance remains a field of `PhysicalLocalSPDPrecisionRootCertificate`. -/
noncomputable def PhysicalLocalSPDInverseSqrtData.covarianceWeightCandidate
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) :
    PhysicalBond d N → PhysicalBond d N → ℝ := by
  classical
  exact fun target source =>
    H.scale⁻¹ *
      ((if target = source then 1 else 0) +
        H.resolventData.resolventAmplitude *
          Real.exp
            (-((H.resolventData.kappa - H.resolventData.sigma) *
              dist target source)))

/-- Candidate positive-root weight for the identity plus inverse-square-root
tail picture.  It is not by itself a certified root kernel bound. -/
noncomputable def PhysicalLocalSPDInverseSqrtData.rootWeightCandidate
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist) :
    PhysicalBond d N → PhysicalBond d N → ℝ := by
  classical
  exact fun target source =>
    (Real.sqrt H.scale)⁻¹ *
      ((if target = source then 1 else 0) +
        H.resolventData.resolventAmplitude *
          Real.exp
            (-((H.resolventData.kappa - H.resolventData.sigma) *
              dist target source)))

/-- The exact remaining fields needed to upgrade local-SPD data into the
existing localized covariance-root certificate.

The record deliberately carries covariance/root kernel bounds and square-root
semantics as source inputs.  Scalar kernel decay alone does not prove those
operator statements. -/
structure PhysicalLocalSPDPrecisionRootCertificate
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    (H : PhysicalLocalSPDInverseSqrtData precision dist)
    (root :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (rootNormBound : ℝ) : Prop where

  covariance_kernel_bound :
    PhysicalCovarianceKernelBound
      H.covariance H.covarianceWeightCandidate

  root_square :
    root.comp root = H.covariance

  root_norm_bound :
    ‖root‖ ≤ rootNormBound

  root_selfAdjoint_form :
    ∀ x y : PhysicalGaugeOneCochain d N Nc,
      inner ℝ x (root y) = inner ℝ (root x) y

  root_psd :
    ∀ y : PhysicalGaugeOneCochain d N Nc,
      0 ≤ inner ℝ y (root y)

  root_kernel_bound :
    PhysicalCovarianceKernelBound
      root H.rootWeightCandidate

/-- Package local-SPD precision data and the remaining root/kernel source
fields into the existing localized covariance-root certificate. -/
theorem PhysicalLocalSPDPrecisionRootCertificate.toLocalizedCovarianceRootCertificate
    {d N Nc : ℕ} [NeZero N]
    {precision :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℝ}
    {H : PhysicalLocalSPDInverseSqrtData precision dist}
    {root :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {rootNormBound : ℝ}
    (C : PhysicalLocalSPDPrecisionRootCertificate H root rootNormBound) :
    PhysicalLocalizedCovarianceRootCertificate
      precision
      H.covariance
      root
      H.coercivityConstant⁻¹
      rootNormBound
      H.covarianceWeightCandidate
      H.rootWeightCandidate := by
  apply physicalLocalizedCovarianceRootCertificate_of_source
  · exact
      { covariance_comp_precision :=
          covarianceOfIsCoerciveCLM_comp_precision
            precision H.coercivityConstant_pos H.precision_coercive
        precision_comp_covariance :=
          precision_comp_covarianceOfIsCoerciveCLM
            precision H.coercivityConstant_pos H.precision_coercive
        covariance_norm_bound :=
          norm_covarianceOfIsCoerciveCLM_le
            precision H.coercivityConstant_pos H.precision_coercive
        covariance_psd :=
          covarianceOfIsCoerciveCLM_psd
            precision H.coercivityConstant_pos H.precision_coercive
        kernel_bound := C.covariance_kernel_bound }
  · exact C.root_square
  · exact C.root_norm_bound
  · exact C.root_selfAdjoint_form
  · exact C.root_psd
  · exact C.root_kernel_bound

end YangMills.RG
