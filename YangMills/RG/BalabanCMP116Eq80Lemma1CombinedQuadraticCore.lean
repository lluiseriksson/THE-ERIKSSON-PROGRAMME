/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116PartialResidualAssembly
import YangMills.RG.BalabanCMP116Eq143To219

/-!
# Quadratic core on the direct/native domain ledger

The terminal CMP116 domain index is the disjoint append of the direct
equation-(80) domains and the native CMP109 Lemma-1 domains.  On the direct
branch, `total` and `residual` are the literal equation-(80) families.  On a
native index, the Lemma-1 activity is placed in both families.  Thus it
remains present in equation (1.36), but cancels exactly from the quadratic
core `total - residual` used in equation (1.43).

This is not a zero extension of the Lemma-1 residual: the sum of the combined
total family contains every native residual literally.  Only its quadratic
core is zero, because the source assigns that sector to `V''_k` rather than
to the fixed-Hessian part.

The terminal compositor below consequently reduces equation (1.43) on the
combined ledger to the physical direct-sector estimate.  No estimate for a
native Hessian, no quotient of domain indices, and no synthetic native
potential is assumed.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Total localized activity on the disjoint direct/native domain ledger. -/
noncomputable def cmp116Eq80Lemma1CombinedTotal
    {m n : ℕ} {E : Type*}
    (directTotal : Fin m → E → ℝ)
    (nativeResidual : Fin n → E → ℝ) :
    Fin (m + n) → E → ℝ :=
  Fin.append directTotal nativeResidual

/-- Source residual on the same disjoint direct/native ledger. -/
noncomputable def cmp116Eq80Lemma1CombinedResidual
    {m n : ℕ} {E : Type*}
    (directResidual : Fin m → E → ℝ)
    (nativeResidual : Fin n → E → ℝ) :
    Fin (m + n) → E → ℝ :=
  Fin.append directResidual nativeResidual

@[simp] theorem cmp116Eq80Lemma1CombinedTotal_direct
    {m n : ℕ} {E : Type*}
    (directTotal : Fin m → E → ℝ)
    (nativeResidual : Fin n → E → ℝ)
    (i : Fin m) :
    cmp116Eq80Lemma1CombinedTotal directTotal nativeResidual
        (Fin.castAdd n i) = directTotal i := by
  simp [cmp116Eq80Lemma1CombinedTotal]

@[simp] theorem cmp116Eq80Lemma1CombinedTotal_native
    {m n : ℕ} {E : Type*}
    (directTotal : Fin m → E → ℝ)
    (nativeResidual : Fin n → E → ℝ)
    (i : Fin n) :
    cmp116Eq80Lemma1CombinedTotal directTotal nativeResidual
        (Fin.natAdd m i) = nativeResidual i := by
  simp [cmp116Eq80Lemma1CombinedTotal]

@[simp] theorem cmp116Eq80Lemma1CombinedResidual_direct
    {m n : ℕ} {E : Type*}
    (directResidual : Fin m → E → ℝ)
    (nativeResidual : Fin n → E → ℝ)
    (i : Fin m) :
    cmp116Eq80Lemma1CombinedResidual directResidual nativeResidual
        (Fin.castAdd n i) = directResidual i := by
  simp [cmp116Eq80Lemma1CombinedResidual]

@[simp] theorem cmp116Eq80Lemma1CombinedResidual_native
    {m n : ℕ} {E : Type*}
    (directResidual : Fin m → E → ℝ)
    (nativeResidual : Fin n → E → ℝ)
    (i : Fin n) :
    cmp116Eq80Lemma1CombinedResidual directResidual nativeResidual
        (Fin.natAdd m i) = nativeResidual i := by
  simp [cmp116Eq80Lemma1CombinedResidual]

/-- The combined total ledger retains all native Lemma-1 activities. -/
theorem sum_cmp116Eq80Lemma1CombinedTotal
    {m n : ℕ} {E : Type*}
    (directTotal : Fin m → E → ℝ)
    (nativeResidual : Fin n → E → ℝ)
    (B : E) :
    (∑ i, cmp116Eq80Lemma1CombinedTotal directTotal nativeResidual i B) =
      (∑ i, directTotal i B) + ∑ i, nativeResidual i B := by
  rw [Fin.sum_univ_add]
  simp

/-- The combined residual ledger retains the same native activities. -/
theorem sum_cmp116Eq80Lemma1CombinedResidual
    {m n : ℕ} {E : Type*}
    (directResidual : Fin m → E → ℝ)
    (nativeResidual : Fin n → E → ℝ)
    (B : E) :
    (∑ i, cmp116Eq80Lemma1CombinedResidual directResidual nativeResidual i B) =
      (∑ i, directResidual i B) + ∑ i, nativeResidual i B := by
  rw [Fin.sum_univ_add]
  simp

/-- On a direct index the combined quadratic core is exactly the direct
quadratic core. -/
@[simp] theorem cmp116Eq142PhysicalQuadraticCore_combined_direct
    {m n d N Nc : ℕ} [NeZero N]
    (directTotal directResidual :
      Fin m → PhysicalGaugeOneCochain d N Nc → ℝ)
    (nativeResidual :
      Fin n → PhysicalGaugeOneCochain d N Nc → ℝ)
    (i : Fin m) (B : PhysicalGaugeOneCochain d N Nc) :
    cmp116Eq142PhysicalQuadraticCore
        (cmp116Eq80Lemma1CombinedTotal directTotal nativeResidual)
        (cmp116Eq80Lemma1CombinedResidual directResidual nativeResidual)
        (Fin.castAdd n i) B =
      cmp116Eq142PhysicalQuadraticCore
        directTotal directResidual i B := by
  simp [cmp116Eq142PhysicalQuadraticCore]

/-- On a native Lemma-1 index the quadratic core is exactly zero, because
the same literal residual occurs in `total` and `residual`. -/
@[simp] theorem cmp116Eq142PhysicalQuadraticCore_combined_native
    {m n d N Nc : ℕ} [NeZero N]
    (directTotal directResidual :
      Fin m → PhysicalGaugeOneCochain d N Nc → ℝ)
    (nativeResidual :
      Fin n → PhysicalGaugeOneCochain d N Nc → ℝ)
    (i : Fin n) (B : PhysicalGaugeOneCochain d N Nc) :
    cmp116Eq142PhysicalQuadraticCore
        (cmp116Eq80Lemma1CombinedTotal directTotal nativeResidual)
        (cmp116Eq80Lemma1CombinedResidual directResidual nativeResidual)
        (Fin.natAdd m i) B = 0 := by
  simp [cmp116Eq142PhysicalQuadraticCore]

/-- Smoothness of the combined core is inherited from the direct sector;
the native cores are constant zero. -/
theorem contDiff_cmp116Eq142PhysicalQuadraticCore_combined
    {m n d N Nc : ℕ} [NeZero N]
    (directTotal directResidual :
      Fin m → PhysicalGaugeOneCochain d N Nc → ℝ)
    (nativeResidual :
      Fin n → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hdirect : ∀ i, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore directTotal directResidual i)) :
    ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore
        (cmp116Eq80Lemma1CombinedTotal directTotal nativeResidual)
        (cmp116Eq80Lemma1CombinedResidual directResidual nativeResidual) y) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · convert hdirect i using 1
    funext B
    exact cmp116Eq142PhysicalQuadraticCore_combined_direct
      directTotal directResidual nativeResidual i B
  · convert (contDiff_const : ContDiff ℝ 2
        (fun _ : PhysicalGaugeOneCochain d N Nc => (0 : ℝ))) using 1
    funext B
    exact cmp116Eq142PhysicalQuadraticCore_combined_native
      directTotal directResidual nativeResidual i B

/-- Equation (1.43) on the combined domain ledger reduces to the physical
direct-sector Hessian estimate.  The native branch is discharged internally
from exact cancellation and positivity of the printed majorant.

The hypothesis is deliberately only the direct equation-(1.43) estimate;
there is no free native Hessian bound. -/
theorem abs_cmp116FDerivHessian_combined_le_eq143
    {m n d N Nc : ℕ} [NeZero N]
    (directTotal directResidual :
      Fin m → PhysicalGaugeOneCochain d N Nc → ℝ)
    (nativeResidual :
      Fin n → PhysicalGaugeOneCochain d N Nc → ℝ)
    (domainMetric : Fin (m + n) → ℕ)
    (domainCard : Fin (m + n) → ℕ)
    (C3 epsilon1 C2 kappa1 : ℝ) (M : ℕ)
    (hamplitude : 0 ≤ C3 * epsilon1)
    (hdirect : ∀ (i : Fin m)
      (B A A' : PhysicalGaugeOneCochain d N Nc) (t : ℝ),
      |cmp116FDerivHessian
        (cmp116Eq142PhysicalQuadraticCore directTotal directResidual i)
        (t • B) A' A| ≤
          cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
            (domainMetric (Fin.castAdd n i) : ℝ)
            (domainCard (Fin.castAdd n i)) * ‖A‖ * ‖A'‖) :
    ∀ (y : Fin (m + n))
      (B A A' : PhysicalGaugeOneCochain d N Nc) (t : ℝ),
      |cmp116FDerivHessian
        (cmp116Eq142PhysicalQuadraticCore
          (cmp116Eq80Lemma1CombinedTotal directTotal nativeResidual)
          (cmp116Eq80Lemma1CombinedResidual directResidual nativeResidual) y)
        (t • B) A' A| ≤
          cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
            (domainMetric y : ℝ) (domainCard y) * ‖A‖ * ‖A'‖ := by
  refine Fin.addCases (fun i B A A' t => ?_) (fun i B A A' t => ?_)
  · have hcore :
        cmp116Eq142PhysicalQuadraticCore
          (cmp116Eq80Lemma1CombinedTotal directTotal nativeResidual)
          (cmp116Eq80Lemma1CombinedResidual directResidual nativeResidual)
          (Fin.castAdd n i) =
            cmp116Eq142PhysicalQuadraticCore directTotal directResidual i := by
      funext X
      exact cmp116Eq142PhysicalQuadraticCore_combined_direct
        directTotal directResidual nativeResidual i X
    rw [hcore]
    exact hdirect i B A A' t
  · have hcore :
        cmp116Eq142PhysicalQuadraticCore
          (cmp116Eq80Lemma1CombinedTotal directTotal nativeResidual)
          (cmp116Eq80Lemma1CombinedResidual directResidual nativeResidual)
          (Fin.natAdd m i) =
            (fun _ : PhysicalGaugeOneCochain d N Nc => (0 : ℝ)) := by
      funext X
      exact cmp116Eq142PhysicalQuadraticCore_combined_native
        directTotal directResidual nativeResidual i X
    rw [hcore]
    simp [cmp116FDerivHessian]
    unfold cmp116Eq143QMajorant
    have hmajorant :
        0 ≤ C3 * epsilon1 * (M : ℝ) ^ 4 * Real.exp (C2 * kappa1) *
          Real.exp (-(1 / 8 : ℝ) * (kappa1 - 1) *
              (domainMetric (Fin.natAdd m i) : ℝ) -
            (1 / 2 : ℝ) * (kappa1 - 1) *
              domainCard (Fin.natAdd m i)) := by
      positivity
    exact mul_nonneg (mul_nonneg hmajorant (norm_nonneg A)) (norm_nonneg A')

end

end YangMills.RG
