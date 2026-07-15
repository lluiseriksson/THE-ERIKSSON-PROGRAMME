/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.KernelSchur

/-!
# CMP116 equation (2.21): localized operator forms

Equation (2.21) controls the three correction forms `R1`, `R2`, and `R3`
from equation (2.16) by the localized energies of the `X` and `B` fields.
This module proves the finite-dimensional analytic implication from a common
exponentially decaying kernel bound:

* quadratic forms are controlled by the corresponding localized energy;
* the mixed form is controlled by half the sum of the two energies;
* the three source forms are controlled jointly without a hidden
  volume-dependent factor;
* the coefficients from equations (2.20), (2.21), and (2.22) can be absorbed
  into the single `alpha5` budget used in equations (2.23)--(2.25).

Honest scope: this module does not prove that the concrete CMP116 operators
`R1`, `R2`, and `R3` satisfy equation (2.16).  It proves the Schur/localization
consequence once those model-specific kernel estimates are supplied.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

private theorem cmp116Eq221_expDecay_quadratic_form_le_localized
    {V : Type*} [Fintype V] [DecidableEq V]
    (Y0 : Finset V)
    {d : V → V → ℝ} {amplitude kappa rowSum : ℝ}
    {K : V → V → ℝ}
    (hamplitude : 0 ≤ amplitude)
    (hsym : ∀ x y, d x y = d y x)
    (hdecay : ExpDecay d amplitude kappa K)
    (hrow : ∀ x, ∑ y, Real.exp (-kappa * d x y) ≤ rowSum)
    (u : V → ℝ) (hsupport : ∀ i, i ∉ Y0 → u i = 0) :
    |∑ x, ∑ y, u x * K x y * u y| ≤
      (amplitude * rowSum) * ∑ x ∈ Y0, u x ^ 2 := by
  have hschur := expDecay_quadratic_form_le
    hamplitude hsym hdecay hrow u
  have hsum : (∑ x, u x ^ 2) = ∑ x ∈ Y0, u x ^ 2 := by
    classical
    refine (Finset.sum_subset (Finset.subset_univ Y0) ?_).symm
    intro i hi hnot
    rw [hsupport i hnot]
    norm_num
  simpa [hsum] using hschur

/-- Localized bilinear Schur estimate.  This is the mixed `R3` step in
equation (2.21): the product of the two `l2` norms is absorbed into half the
sum of their squared localized energies. -/
theorem cmp116Eq221_expDecay_bilinear_le_localized
    {V : Type*} [Fintype V] [DecidableEq V]
    (BX : Finset V) (BB : Finset V)
    {d : V → V → ℝ} {amplitude kappa rowSum : ℝ}
    {K : V → V → ℝ}
    (hamplitude : 0 ≤ amplitude) (hrowSum : 0 ≤ rowSum)
    (hsym : ∀ x y, d x y = d y x)
    (hdecay : ExpDecay d amplitude kappa K)
    (hrow : ∀ x, ∑ y, Real.exp (-kappa * d x y) ≤ rowSum)
    (u v : V → ℝ)
    (hsupportU : ∀ i, i ∉ BB → u i = 0)
    (hsupportV : ∀ i, i ∉ BX → v i = 0) :
    |∑ x, ∑ y, u x * K x y * v y| ≤
      (amplitude * rowSum) / 2 *
        ((∑ x ∈ BB, u x ^ 2) + ∑ x ∈ BX, v x ^ 2) := by
  have hop := expDecay_op_bilinear_le
    hamplitude hrowSum hsym hdecay hrow u v
  have hsumU : (∑ x, u x ^ 2) = ∑ x ∈ BB, u x ^ 2 := by
    classical
    refine (Finset.sum_subset (Finset.subset_univ BB) ?_).symm
    intro i hi hnot
    rw [hsupportU i hnot]
    norm_num
  have hsumV : (∑ x, v x ^ 2) = ∑ x ∈ BX, v x ^ 2 := by
    classical
    refine (Finset.sum_subset (Finset.subset_univ BX) ?_).symm
    intro i hi hnot
    rw [hsupportV i hnot]
    norm_num
  let energyU : ℝ := ∑ x ∈ BB, u x ^ 2
  let energyV : ℝ := ∑ x ∈ BX, v x ^ 2
  have henergyU : 0 ≤ energyU := by
    dsimp [energyU]
    positivity
  have henergyV : 0 ≤ energyV := by
    dsimp [energyV]
    positivity
  have hsqrt :
      Real.sqrt energyU * Real.sqrt energyV ≤ (energyU + energyV) / 2 := by
    have h := two_mul_le_add_sq (Real.sqrt energyU) (Real.sqrt energyV)
    rw [Real.sq_sqrt henergyU, Real.sq_sqrt henergyV] at h
    linarith
  rw [hsumU, hsumV] at hop
  change |∑ x, ∑ y, u x * K x y * v y| ≤
    (amplitude * rowSum) / 2 * (energyU + energyV)
  calc
    |∑ x, ∑ y, u x * K x y * v y| ≤
        amplitude * rowSum *
          (Real.sqrt energyU * Real.sqrt energyV) := hop
    _ ≤ amplitude * rowSum * ((energyU + energyV) / 2) := by
      exact mul_le_mul_of_nonneg_left hsqrt
        (mul_nonneg hamplitude hrowSum)
    _ = (amplitude * rowSum) / 2 * (energyU + energyV) := by ring

/-- Joint equation-(2.21) estimate for the two quadratic corrections and the
mixed correction.  The constant implicit in the source's `O(1)` is exposed:
three kernels with common Schur cost `amplitude * rowSum` cost exactly that
coefficient times the sum of the two localized energies. -/
theorem cmp116Eq221_three_operator_forms_le_localized
    {V : Type*} [Fintype V] [DecidableEq V]
    (BX : Finset V) (BB : Finset V)
    {d : V → V → ℝ} {amplitude kappa rowSum : ℝ}
    (R1 R2 R3 : V → V → ℝ)
    (hamplitude : 0 ≤ amplitude) (hrowSum : 0 ≤ rowSum)
    (hsym : ∀ x y, d x y = d y x)
    (hdecay1 : ExpDecay d amplitude kappa R1)
    (hdecay2 : ExpDecay d amplitude kappa R2)
    (hdecay3 : ExpDecay d amplitude kappa R3)
    (hrow : ∀ x, ∑ y, Real.exp (-kappa * d x y) ≤ rowSum)
    (X B : V → ℝ)
    (hsupportX : ∀ i, i ∉ BX → X i = 0)
    (hsupportB : ∀ i, i ∉ BB → B i = 0) :
    (1 / 2 : ℝ) * |∑ x, ∑ y, X x * R1 x y * X y| +
        (1 / 2 : ℝ) * |∑ x, ∑ y, B x * R2 x y * B y| +
        |∑ x, ∑ y, B x * R3 x y * X y| ≤
      (amplitude * rowSum) *
        ((∑ x ∈ BX, X x ^ 2) + ∑ x ∈ BB, B x ^ 2) := by
  have h1 := cmp116Eq221_expDecay_quadratic_form_le_localized
    BX hamplitude hsym hdecay1 hrow X hsupportX
  have h2 := cmp116Eq221_expDecay_quadratic_form_le_localized
    BB hamplitude hsym hdecay2 hrow B hsupportB
  have h3 := cmp116Eq221_expDecay_bilinear_le_localized
    BX BB hamplitude hrowSum hsym hdecay3 hrow B X hsupportB hsupportX
  linarith

/-- Scalar coefficient ledger for equations (2.20)--(2.22).  The potential
term acts only on the `B` energy, the operator corrections act on both `X` and
`B`, and the cutoff energy is contained in the `B` localization. -/
theorem cmp116Eq220_eq221_eq222_absorb_into_alpha5
    {potentialTerm operatorTerm potentialRate operatorRate cutoff alpha5
      energyP energyX energyB
      residual20 residual21 : ℝ}
    (hpotential :
      potentialTerm ≤ potentialRate / 2 * energyB + residual20)
    (hoperator :
      operatorTerm ≤ operatorRate / 2 * (energyX + energyB) + residual21)
    (henergy : energyP ≤ energyB)
    (hpotentialRate : 0 ≤ potentialRate)
    (hcutoff : 0 ≤ cutoff)
    (henergyX : 0 ≤ energyX) (henergyB : 0 ≤ energyB)
    (hbudget : potentialRate + operatorRate + cutoff ≤ alpha5) :
    potentialTerm + operatorTerm + cutoff / 2 * energyP ≤
      alpha5 / 2 * (energyX + energyB) + residual20 + residual21 := by
  have henergyBTotal : energyB ≤ energyX + energyB := by linarith
  have hpotential' :
      potentialTerm ≤ potentialRate / 2 * (energyX + energyB) + residual20 := by
    exact hpotential.trans (by
      gcongr)
  have hcutoffEnergy :
      cutoff / 2 * energyP ≤ cutoff / 2 * (energyX + energyB) := by
    have hEP : energyP ≤ energyX + energyB := le_trans henergy henergyBTotal
    exact mul_le_mul_of_nonneg_left hEP (by positivity)
  have htotal : 0 ≤ energyX + energyB := add_nonneg henergyX henergyB
  have hbudgetMul :
      (potentialRate + operatorRate + cutoff) / 2 * (energyX + energyB) ≤
        alpha5 / 2 * (energyX + energyB) := by
    exact mul_le_mul_of_nonneg_right (by linarith) htotal
  have hcoefficient :
      potentialRate / 2 * (energyX + energyB) +
          operatorRate / 2 * (energyX + energyB) +
          cutoff / 2 * (energyX + energyB) ≤
        alpha5 / 2 * (energyX + energyB) := by
    calc
      potentialRate / 2 * (energyX + energyB) +
            operatorRate / 2 * (energyX + energyB) +
            cutoff / 2 * (energyX + energyB) =
          (potentialRate + operatorRate + cutoff) / 2 *
            (energyX + energyB) := by ring
      _ ≤ alpha5 / 2 * (energyX + energyB) := hbudgetMul
  linarith

end

end YangMills.RG
