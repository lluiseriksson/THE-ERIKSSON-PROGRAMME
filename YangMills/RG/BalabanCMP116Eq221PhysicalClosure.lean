/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq216PhysicalClosure
import YangMills.RG.BalabanCMP116Eq221OperatorForms

/-!
# Physical consumption of the CMP116 equation-(2.16) certificate

The kernel certificates produced by the interacting Wilson analysis are
block-valued: a source bond carries the whole `su(Nc)` coordinate vector.
This module applies the Schur argument at that block level.  Consequently
equation (2.21) is obtained without flattening Lie coordinates and without an
artificial factor `Nc² - 1`.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero N]

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

private theorem physical_exponential_kernel_pointwise_sum_bound
    (C : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A κ : ℝ}
    (hC : PhysicalCovarianceExponentialKernelBound C dist A κ)
    (X : PhysicalGaugeOneCochain d N Nc)
    (target : PhysicalBond d N) :
    ‖C X target‖ ≤
      ∑ source : PhysicalBond d N,
        A * Real.exp (-(κ * (dist target source : ℝ))) * ‖X source‖ := by
  have hdecomp :
      C X =
        ∑ source : PhysicalBond d N,
          C (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source (X source)) := by
    rw [← map_sum, sum_singlePhysicalBondCochain_eq]
  have happ :
      C X target =
        ∑ source : PhysicalBond d N,
          C (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source (X source)) target := by
    rw [hdecomp, physicalCochain_sum_apply]
  rw [happ]
  exact (norm_sum_le _ _).trans <|
    Finset.sum_le_sum fun source _ => hC.2.2 source target (X source)

/-- A block-valued physical exponential kernel controls its localized
quadratic form with the ordinary scalar Schur constant. -/
theorem physicalExponentialKernel_quadratic_form_le_localized
    (Y0 : Finset (PhysicalBond d N))
    (C : PhysicalEndomorphism d N Nc)
    {A κ rowSum : ℝ}
    (hC : PhysicalCovarianceExponentialKernelBound C physicalBondDist A κ)
    (hrow :
      ∀ target : PhysicalBond d N,
        ∑ source : PhysicalBond d N,
          Real.exp (-(κ * (physicalBondDist target source : ℝ))) ≤ rowSum)
    (X : PhysicalGaugeOneCochain d N Nc)
    (hsupport : ∀ i, i ∉ Y0 → X i = 0) :
    |inner ℝ X (C X)| ≤
      (A * rowSum) * ∑ i ∈ Y0, ‖X i‖ ^ 2 := by
  have hinner :
      |inner ℝ X (C X)| ≤
        ∑ target : PhysicalBond d N,
          ‖X target‖ * ‖C X target‖ := by
    rw [PiLp.inner_apply]
    exact (Finset.abs_sum_le_sum_abs _ _).trans <|
      Finset.sum_le_sum fun target _ => abs_real_inner_le_norm _ _
  have hpoint :
      ∑ target : PhysicalBond d N,
          ‖X target‖ * ‖C X target‖ ≤
        ∑ target : PhysicalBond d N,
          ∑ source : PhysicalBond d N,
            ‖X target‖ *
              (A * Real.exp
                (-(κ * (physicalBondDist target source : ℝ)))) *
              ‖X source‖ := by
    refine Finset.sum_le_sum fun target _ => ?_
    calc
      ‖X target‖ * ‖C X target‖ ≤
          ‖X target‖ *
            (∑ source : PhysicalBond d N,
              A * Real.exp
                (-(κ * (physicalBondDist target source : ℝ))) *
              ‖X source‖) :=
        mul_le_mul_of_nonneg_left
          (physical_exponential_kernel_pointwise_sum_bound
            C physicalBondDist hC X target)
          (norm_nonneg _)
      _ = ∑ source : PhysicalBond d N,
            ‖X target‖ *
              (A * Real.exp
                (-(κ * (physicalBondDist target source : ℝ)))) *
              ‖X source‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro source _
        ring
  let K : PhysicalBond d N → PhysicalBond d N → ℝ :=
    fun target source =>
      A * Real.exp (-(κ * (physicalBondDist target source : ℝ)))
  have hK :
      ExpDecay
        (fun target source => (physicalBondDist target source : ℝ))
        A κ K := by
    intro target source
    dsimp [K]
    rw [abs_of_nonneg (mul_nonneg hC.1 (Real.exp_pos _).le)]
    simp only [neg_mul]
    exact le_rfl
  have hschur := expDecay_quadratic_form_le
    hC.1
    (fun target source => by
      exact_mod_cast physicalBondDist_comm target source)
    hK
    (fun target => by
      simpa only [neg_mul] using hrow target)
    (fun target => ‖X target‖)
  have hnonneg :
      0 ≤ ∑ target : PhysicalBond d N,
        ∑ source : PhysicalBond d N,
          ‖X target‖ * K target source * ‖X source‖ := by
    exact Finset.sum_nonneg fun target _ =>
      Finset.sum_nonneg fun source _ => by
        dsimp [K]
        exact mul_nonneg
          (mul_nonneg (norm_nonneg _)
            (mul_nonneg hC.1 (Real.exp_pos _).le))
          (norm_nonneg _)
  have hglobal :
      ∑ target : PhysicalBond d N,
          ∑ source : PhysicalBond d N,
            ‖X target‖ *
              (A * Real.exp
                (-(κ * (physicalBondDist target source : ℝ)))) *
              ‖X source‖ ≤
        (A * rowSum) *
          ∑ target : PhysicalBond d N, ‖X target‖ ^ 2 := by
    simpa [K, abs_of_nonneg hnonneg] using hschur
  have hlocalized :
      (∑ target : PhysicalBond d N, ‖X target‖ ^ 2) =
        ∑ target ∈ Y0, ‖X target‖ ^ 2 := by
    classical
    refine (Finset.sum_subset (Finset.subset_univ Y0) ?_).symm
    intro target _ hnot
    rw [hsupport target hnot, norm_zero, zero_pow]
    norm_num
  exact hinner.trans <| hpoint.trans <| by
    simpa [hlocalized] using hglobal

/-- The block-valued mixed Schur estimate.  Its right-hand side is already in
the half-sum form required for the `R₃` contribution to equation (2.21). -/
theorem physicalExponentialKernel_bilinear_form_le_localized
    (BX BB : Finset (PhysicalBond d N))
    (C : PhysicalEndomorphism d N Nc)
    {A κ rowSum : ℝ}
    (hrowSum : 0 ≤ rowSum)
    (hC : PhysicalCovarianceExponentialKernelBound C physicalBondDist A κ)
    (hrow :
      ∀ target : PhysicalBond d N,
        ∑ source : PhysicalBond d N,
          Real.exp (-(κ * (physicalBondDist target source : ℝ))) ≤ rowSum)
    (X B : PhysicalGaugeOneCochain d N Nc)
    (hsupportX : ∀ i, i ∉ BX → X i = 0)
    (hsupportB : ∀ i, i ∉ BB → B i = 0) :
    |inner ℝ B (C X)| ≤
      (A * rowSum) / 2 *
        ((∑ i ∈ BB, ‖B i‖ ^ 2) + ∑ i ∈ BX, ‖X i‖ ^ 2) := by
  have hinner :
      |inner ℝ B (C X)| ≤
        ∑ target : PhysicalBond d N,
          ‖B target‖ * ‖C X target‖ := by
    rw [PiLp.inner_apply]
    exact (Finset.abs_sum_le_sum_abs _ _).trans <|
      Finset.sum_le_sum fun target _ => abs_real_inner_le_norm _ _
  have hpoint :
      ∑ target : PhysicalBond d N,
          ‖B target‖ * ‖C X target‖ ≤
        ∑ target : PhysicalBond d N,
          ∑ source : PhysicalBond d N,
            ‖B target‖ *
              (A * Real.exp
                (-(κ * (physicalBondDist target source : ℝ)))) *
              ‖X source‖ := by
    refine Finset.sum_le_sum fun target _ => ?_
    calc
      ‖B target‖ * ‖C X target‖ ≤
          ‖B target‖ *
            (∑ source : PhysicalBond d N,
              A * Real.exp
                (-(κ * (physicalBondDist target source : ℝ))) *
              ‖X source‖) :=
        mul_le_mul_of_nonneg_left
          (physical_exponential_kernel_pointwise_sum_bound
            C physicalBondDist hC X target)
          (norm_nonneg _)
      _ = ∑ source : PhysicalBond d N,
            ‖B target‖ *
              (A * Real.exp
                (-(κ * (physicalBondDist target source : ℝ)))) *
              ‖X source‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro source _
        ring
  let K : PhysicalBond d N → PhysicalBond d N → ℝ :=
    fun target source =>
      A * Real.exp (-(κ * (physicalBondDist target source : ℝ)))
  have hK :
      ExpDecay
        (fun target source => (physicalBondDist target source : ℝ))
        A κ K := by
    intro target source
    dsimp [K]
    rw [abs_of_nonneg (mul_nonneg hC.1 (Real.exp_pos _).le)]
    simp only [neg_mul]
    exact le_rfl
  have hschur := expDecay_op_bilinear_le
    hC.1 hrowSum
    (fun target source => by
      exact_mod_cast physicalBondDist_comm target source)
    hK
    (fun target => by
      simpa only [neg_mul] using hrow target)
    (fun target => ‖B target‖)
    (fun source => ‖X source‖)
  have hnonneg :
      0 ≤ ∑ target : PhysicalBond d N,
        ∑ source : PhysicalBond d N,
          ‖B target‖ * K target source * ‖X source‖ := by
    exact Finset.sum_nonneg fun target _ =>
      Finset.sum_nonneg fun source _ => by
        dsimp [K]
        exact mul_nonneg
          (mul_nonneg (norm_nonneg _)
            (mul_nonneg hC.1 (Real.exp_pos _).le))
          (norm_nonneg _)
  have hglobal :
      ∑ target : PhysicalBond d N,
          ∑ source : PhysicalBond d N,
            ‖B target‖ *
              (A * Real.exp
                (-(κ * (physicalBondDist target source : ℝ)))) *
              ‖X source‖ ≤
        A * rowSum *
          (Real.sqrt (∑ target : PhysicalBond d N, ‖B target‖ ^ 2) *
            Real.sqrt (∑ source : PhysicalBond d N, ‖X source‖ ^ 2)) := by
    simpa [K, abs_of_nonneg hnonneg] using hschur
  let energyB : ℝ := ∑ target ∈ BB, ‖B target‖ ^ 2
  let energyX : ℝ := ∑ source ∈ BX, ‖X source‖ ^ 2
  have hsumB :
      (∑ target : PhysicalBond d N, ‖B target‖ ^ 2) = energyB := by
    dsimp [energyB]
    classical
    refine (Finset.sum_subset (Finset.subset_univ BB) ?_).symm
    intro target _ hnot
    rw [hsupportB target hnot, norm_zero, zero_pow]
    norm_num
  have hsumX :
      (∑ source : PhysicalBond d N, ‖X source‖ ^ 2) = energyX := by
    dsimp [energyX]
    classical
    refine (Finset.sum_subset (Finset.subset_univ BX) ?_).symm
    intro source _ hnot
    rw [hsupportX source hnot, norm_zero, zero_pow]
    norm_num
  have henergyB : 0 ≤ energyB := by
    dsimp [energyB]
    positivity
  have henergyX : 0 ≤ energyX := by
    dsimp [energyX]
    positivity
  have hsqrt :
      Real.sqrt energyB * Real.sqrt energyX ≤
        (energyB + energyX) / 2 := by
    have h := two_mul_le_add_sq (Real.sqrt energyB) (Real.sqrt energyX)
    rw [Real.sq_sqrt henergyB, Real.sq_sqrt henergyX] at h
    linarith
  have hcoefficient : 0 ≤ A * rowSum :=
    mul_nonneg hC.1 hrowSum
  calc
    |inner ℝ B (C X)| ≤
        ∑ target : PhysicalBond d N,
          ‖B target‖ * ‖C X target‖ := hinner
    _ ≤ ∑ target : PhysicalBond d N,
          ∑ source : PhysicalBond d N,
            ‖B target‖ *
              (A * Real.exp
                (-(κ * (physicalBondDist target source : ℝ)))) *
              ‖X source‖ := hpoint
    _ ≤ A * rowSum *
          (Real.sqrt energyB * Real.sqrt energyX) := by
      simpa [hsumB, hsumX] using hglobal
    _ ≤ A * rowSum * ((energyB + energyX) / 2) :=
      mul_le_mul_of_nonneg_left hsqrt hcoefficient
    _ = (A * rowSum) / 2 * (energyB + energyX) := by ring

/-- The common physical equation-(2.16) certificate implies the joint
equation-(2.21) localized-energy estimate, without an ambient-volume or
Lie-coordinate multiplicity factor. -/
theorem CMP116Eq216PhysicalKernelCertificate.three_operator_forms_le_localized
    {R₁ R₂ R₃ : PhysicalEndomorphism d N Nc}
    (cert : CMP116Eq216PhysicalKernelCertificate
      R₁ R₂ R₃ physicalBondDist)
    (BX BB : Finset (PhysicalBond d N))
    (rowSum : ℝ)
    (hrowSum : 0 ≤ rowSum)
    (hrow :
      ∀ target : PhysicalBond d N,
        ∑ source : PhysicalBond d N,
          Real.exp
            (-(cert.rate *
              (physicalBondDist target source : ℝ))) ≤ rowSum)
    (X B : PhysicalGaugeOneCochain d N Nc)
    (hsupportX : ∀ i, i ∉ BX → X i = 0)
    (hsupportB : ∀ i, i ∉ BB → B i = 0) :
    (1 / 2 : ℝ) * |inner ℝ X (R₁ X)| +
        (1 / 2 : ℝ) * |inner ℝ B (R₂ B)| +
        |inner ℝ B (R₃ X)| ≤
      (cert.amplitude * rowSum) *
        ((∑ i ∈ BX, ‖X i‖ ^ 2) + ∑ i ∈ BB, ‖B i‖ ^ 2) := by
  have h₁ := physicalExponentialKernel_quadratic_form_le_localized
    BX R₁ cert.r1_bound hrow X hsupportX
  have h₂ := physicalExponentialKernel_quadratic_form_le_localized
    BB R₂ cert.r2_bound hrow B hsupportB
  have h₃ := physicalExponentialKernel_bilinear_form_le_localized
    BX BB R₃ hrowSum cert.r3_bound hrow X B hsupportX hsupportB
  linarith

/-- Explicit volume-uniform row-sum constant consumed by the physical
equation-(2.21) endpoint. -/
def cmp116Eq221PhysicalRowSum (d : ℕ) (κ : ℝ) : ℝ :=
  (((2 ^ d) * d : ℕ) : ℝ) *
    (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-κ))⁻¹

/-- Fully geometric consumption of the common equation-(2.16) certificate:
the row sum is generated internally from the physical bond metric. -/
theorem CMP116Eq216PhysicalKernelCertificate.three_operator_forms_le_localized_geometric
    [NeZero d]
    {R₁ R₂ R₃ : PhysicalEndomorphism d N Nc}
    (cert : CMP116Eq216PhysicalKernelCertificate
      R₁ R₂ R₃ physicalBondDist)
    (hgeom :
      ((2 ^ d : ℕ) : ℝ) * Real.exp (-cert.rate) < 1)
    (BX BB : Finset (PhysicalBond d N))
    (X B : PhysicalGaugeOneCochain d N Nc)
    (hsupportX : ∀ i, i ∉ BX → X i = 0)
    (hsupportB : ∀ i, i ∉ BB → B i = 0) :
    (1 / 2 : ℝ) * |inner ℝ X (R₁ X)| +
        (1 / 2 : ℝ) * |inner ℝ B (R₂ B)| +
        |inner ℝ B (R₃ X)| ≤
      (cert.amplitude *
          cmp116Eq221PhysicalRowSum d cert.rate) *
        ((∑ i ∈ BX, ‖X i‖ ^ 2) + ∑ i ∈ BB, ‖B i‖ ^ 2) := by
  have hden :
      0 < 1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-cert.rate) :=
    sub_pos.mpr hgeom
  have hrowSum :
      0 ≤ cmp116Eq221PhysicalRowSum d cert.rate := by
    exact mul_nonneg (by positivity) (inv_nonneg.mpr hden.le)
  exact cert.three_operator_forms_le_localized
    BX BB (cmp116Eq221PhysicalRowSum d cert.rate) hrowSum
    (fun target => by
      simpa [cmp116Eq221PhysicalRowSum] using
        physicalBondDist_exp_sum_le_geometric
          (d := d) (N := N) target hgeom)
    X B hsupportX hsupportB

/-- Direct physical absorption of equations (2.20)--(2.22) into the
`alpha5` budget.  The equation-(2.21) premise is generated internally from
the common physical kernel certificate, with operator rate
`2 * amplitude * rowSum`. -/
theorem CMP116Eq216PhysicalKernelCertificate.three_operator_forms_absorb_into_alpha5_geometric
    [NeZero d]
    {R₁ R₂ R₃ : PhysicalEndomorphism d N Nc}
    (cert : CMP116Eq216PhysicalKernelCertificate
      R₁ R₂ R₃ physicalBondDist)
    (hgeom :
      ((2 ^ d : ℕ) : ℝ) * Real.exp (-cert.rate) < 1)
    (BX BB : Finset (PhysicalBond d N))
    (X B : PhysicalGaugeOneCochain d N Nc)
    (hsupportX : ∀ i, i ∉ BX → X i = 0)
    (hsupportB : ∀ i, i ∉ BB → B i = 0)
    {potentialTerm potentialRate cutoff alpha5 energyP residual20 : ℝ}
    (hpotential :
      potentialTerm ≤
        potentialRate / 2 * (∑ i ∈ BB, ‖B i‖ ^ 2) + residual20)
    (henergy : energyP ≤ ∑ i ∈ BB, ‖B i‖ ^ 2)
    (hpotentialRate : 0 ≤ potentialRate)
    (hcutoff : 0 ≤ cutoff)
    (hbudget :
      potentialRate +
          2 * (cert.amplitude *
            cmp116Eq221PhysicalRowSum d cert.rate) +
          cutoff ≤ alpha5) :
    potentialTerm +
          ((1 / 2 : ℝ) * |inner ℝ X (R₁ X)| +
            (1 / 2 : ℝ) * |inner ℝ B (R₂ B)| +
            |inner ℝ B (R₃ X)|) +
          cutoff / 2 * energyP ≤
      alpha5 / 2 *
          ((∑ i ∈ BX, ‖X i‖ ^ 2) +
            ∑ i ∈ BB, ‖B i‖ ^ 2) +
        residual20 := by
  let energyX : ℝ := ∑ i ∈ BX, ‖X i‖ ^ 2
  let energyB : ℝ := ∑ i ∈ BB, ‖B i‖ ^ 2
  let operatorTerm : ℝ :=
    (1 / 2 : ℝ) * |inner ℝ X (R₁ X)| +
      (1 / 2 : ℝ) * |inner ℝ B (R₂ B)| +
      |inner ℝ B (R₃ X)|
  let operatorRate : ℝ :=
    2 * (cert.amplitude *
      cmp116Eq221PhysicalRowSum d cert.rate)
  have hoperatorRaw :=
    cert.three_operator_forms_le_localized_geometric
      hgeom BX BB X B hsupportX hsupportB
  have hoperator :
      operatorTerm ≤ operatorRate / 2 * (energyX + energyB) := by
    dsimp [operatorTerm, operatorRate, energyX, energyB]
    nlinarith
  have hresult := cmp116Eq220_eq221_eq222_absorb_into_alpha5
    (potentialTerm := potentialTerm)
    (operatorTerm := operatorTerm)
    (potentialRate := potentialRate)
    (operatorRate := operatorRate)
    (cutoff := cutoff)
    (alpha5 := alpha5)
    (energyP := energyP)
    (energyX := energyX)
    (energyB := energyB)
    (residual20 := residual20)
    (residual21 := 0)
    (by simpa [energyB] using hpotential)
    (by simpa using hoperator)
    (by simpa [energyB] using henergy)
    hpotentialRate hcutoff
    (by
      dsimp [energyX]
      positivity)
    (by
      dsimp [energyB]
      positivity)
    (by simpa [operatorRate] using hbudget)
  simpa [operatorTerm, energyX, energyB] using hresult

end

end YangMills.RG
