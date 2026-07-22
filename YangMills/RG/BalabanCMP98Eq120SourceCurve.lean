/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq118SourceCurve

/-!
# The endpoint-conjugated source curve of CMP98 (120)

CMP98 (120) conjugates the central curve of (118) by the entrance and exit
parallel transports.  At first order the two endpoint factors are the
exponentials of the negative averaged return-contour variations.  This file
constructs that literal based curve and derives the already stated endpoint
correction instead of accepting it as an independent summand.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq120SourceMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Averaged entrance variation appearing with a minus sign in (120). -/
def cmp98Eq120EntranceAverage
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      cmp98Eq124EntrancePrefixRightVariation U A b x

/-- Averaged oriented return-contour variation.  Its source orientation is
already contained in `cmp98Eq124ExitPrefixRightVariation`. -/
def cmp98Eq120ExitAverage
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      cmp98Eq124ExitPrefixRightVariation U A b x

/-- The previously assembled endpoint correction is exactly the sum of the
two negative averaged endpoint generators. -/
theorem cmp98Eq120PhysicalEndpointCorrection_eq_neg_averages
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq120PhysicalEndpointCorrection U A b =
      -cmp98Eq120EntranceAverage U A b -
        cmp98Eq120ExitAverage U A b := by
  unfold cmp98Eq120PhysicalEndpointCorrection cmp98Eq120EntranceAverage
    cmp98Eq120ExitAverage
  have hsum :
      (∑ x ∈ blockOf M N' b.1,
          (0 - cmp98Eq124EntrancePrefixRightVariation U A b x -
            cmp98Eq124ExitPrefixRightVariation U A b x)) =
        -(∑ x ∈ blockOf M N' b.1,
            cmp98Eq124EntrancePrefixRightVariation U A b x) -
          ∑ x ∈ blockOf M N' b.1,
            cmp98Eq124ExitPrefixRightVariation U A b x := by
    induction blockOf M N' b.1 using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih =>
        simp only [Finset.sum_insert, hx, not_false_eq_true]
        rw [ih]
        abel
  rw [hsum]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul,
    Matrix.neg_apply]
  ring

/-- Four factors of the endpoint-conjugated first-order curve in (120). -/
def cmp98Eq120SourceFactors
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ :=
  ![fun t => NormedSpace.exp
      (t • (-cmp98Eq120EntranceAverage U A b)),
    cmp98Eq118SourceCurve U A b,
    fun t => NormedSpace.exp
      (t • (-cmp98Eq120ExitAverage U A b)),
    fun _ => 1]

/-- First variations of the four endpoint-conjugated factors. -/
def cmp98Eq120SourceFactorVariations
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ :=
  ![fun _ => -cmp98Eq120EntranceAverage U A b,
    fun _ => fourFactorFirst (cmp98Eq118SourceFactors U A b)
      (cmp98Eq118SourceFactorVariations U A b) 0,
    fun _ => -cmp98Eq120ExitAverage U A b,
    fun _ => 0]

@[simp] theorem cmp98Eq120SourceFactors_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq120SourceFactors U A b 0 t = NormedSpace.exp
      (t • (-cmp98Eq120EntranceAverage U A b)) := rfl

@[simp] theorem cmp98Eq120SourceFactors_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq120SourceFactors U A b 1 t =
      cmp98Eq118SourceCurve U A b t := rfl

@[simp] theorem cmp98Eq120SourceFactors_two
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq120SourceFactors U A b 2 t = NormedSpace.exp
      (t • (-cmp98Eq120ExitAverage U A b)) := rfl

@[simp] theorem cmp98Eq120SourceFactors_three
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq120SourceFactors U A b 3 t = 1 := rfl

@[simp] theorem cmp98Eq120SourceFactorVariations_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq120SourceFactorVariations U A b 0 t =
      -cmp98Eq120EntranceAverage U A b := rfl

@[simp] theorem cmp98Eq120SourceFactorVariations_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq120SourceFactorVariations U A b 1 t =
      fourFactorFirst (cmp98Eq118SourceFactors U A b)
        (cmp98Eq118SourceFactorVariations U A b) 0 := rfl

@[simp] theorem cmp98Eq120SourceFactorVariations_two
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq120SourceFactorVariations U A b 2 t =
      -cmp98Eq120ExitAverage U A b := rfl

@[simp] theorem cmp98Eq120SourceFactorVariations_three
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq120SourceFactorVariations U A b 3 t = 0 := rfl

/-- Literal endpoint-conjugated first-order curve corresponding to (120). -/
def cmp98Eq120SourceCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  fourFactorProduct (cmp98Eq120SourceFactors U A b) t

/-- Each endpoint-conjugated factor has its stated derivative. -/
theorem hasDerivAt_cmp98Eq120SourceFactors
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (i : Fin 4) :
    HasDerivAt (cmp98Eq120SourceFactors U A b i)
      (cmp98Eq120SourceFactorVariations U A b i 0) 0 := by
  fin_cases i
  · have h :=
      hasDerivAt_exp_smul_const (-cmp98Eq120EntranceAverage U A b) (0 : ℝ)
    have h' : HasDerivAt
        (fun t : ℝ => NormedSpace.exp
          (t • (-cmp98Eq120EntranceAverage U A b)))
        (-cmp98Eq120EntranceAverage U A b) 0 := by
      have hexp0 : NormedSpace.exp
          ((0 : ℝ) • (-cmp98Eq120EntranceAverage U A b)) = 1 := by
        have hzero : (0 : ℝ) • (-cmp98Eq120EntranceAverage U A b) = 0 :=
          zero_smul ℝ _
        rw [hzero, NormedSpace.exp_zero]
      have hder : NormedSpace.exp
            ((0 : ℝ) • (-cmp98Eq120EntranceAverage U A b)) *
          (-cmp98Eq120EntranceAverage U A b) =
            -cmp98Eq120EntranceAverage U A b := by
        rw [hexp0, one_mul]
      exact h.congr_deriv hder
    simpa only [cmp98Eq120SourceFactors_zero,
      cmp98Eq120SourceFactorVariations_zero] using h'
  · exact hasDerivAt_cmp98Eq118SourceCurve U A b hsmall
  · have h :=
      hasDerivAt_exp_smul_const (-cmp98Eq120ExitAverage U A b) (0 : ℝ)
    have h' : HasDerivAt
        (fun t : ℝ => NormedSpace.exp
          (t • (-cmp98Eq120ExitAverage U A b)))
        (-cmp98Eq120ExitAverage U A b) 0 := by
      have hexp0 : NormedSpace.exp
          ((0 : ℝ) • (-cmp98Eq120ExitAverage U A b)) = 1 := by
        have hzero : (0 : ℝ) • (-cmp98Eq120ExitAverage U A b) = 0 :=
          zero_smul ℝ _
        rw [hzero, NormedSpace.exp_zero]
      have hder : NormedSpace.exp
            ((0 : ℝ) • (-cmp98Eq120ExitAverage U A b)) *
          (-cmp98Eq120ExitAverage U A b) =
            -cmp98Eq120ExitAverage U A b := by
        rw [hexp0, one_mul]
      exact h.congr_deriv hder
    simpa only [cmp98Eq120SourceFactors_two,
      cmp98Eq120SourceFactorVariations_two] using h'
  · simpa only [cmp98Eq120SourceFactors, cmp98Eq120SourceFactorVariations,
        Matrix.cons_val_three] using
      (hasDerivAt_const (x := (0 : ℝ))
        (c := (1 : Matrix (Fin Nc) (Fin Nc) ℂ)))

/-- Structural derivative of the complete source curve of (120). -/
theorem hasDerivAt_cmp98Eq120SourceCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    HasDerivAt (cmp98Eq120SourceCurve U A b)
      (fourFactorFirst (cmp98Eq120SourceFactors U A b)
        (cmp98Eq120SourceFactorVariations U A b) 0) 0 := by
  exact hasDerivAt_fourFactorProduct
    (cmp98Eq120SourceFactors U A b)
    (cmp98Eq120SourceFactorVariations U A b) 0
    (hasDerivAt_cmp98Eq120SourceFactors U A b hsmall)

/-- The complete endpoint-conjugated source curve is based at identity. -/
theorem cmp98Eq120SourceCurve_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq120SourceCurve U A b 0 = 1 := by
  simp only [cmp98Eq120SourceCurve, fourFactorProduct,
    cmp98Eq120SourceFactors_zero, cmp98Eq120SourceFactors_one,
    cmp98Eq120SourceFactors_two, cmp98Eq120SourceFactors_three]
  have hzeroE : (0 : ℝ) • (-cmp98Eq120EntranceAverage U A b) = 0 :=
    zero_smul ℝ _
  have hzeroX : (0 : ℝ) • (-cmp98Eq120ExitAverage U A b) = 0 :=
    zero_smul ℝ _
  rw [hzeroE, hzeroX, NormedSpace.exp_zero,
    cmp98Eq118SourceCurve_zero U A b]
  simp

/-- First variation of (120): entrance, central (118), and exit terms. -/
theorem cmp98Eq120SourceFirstVariation_eq
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    fourFactorFirst (cmp98Eq120SourceFactors U A b)
        (cmp98Eq120SourceFactorVariations U A b) 0 =
      -cmp98Eq120EntranceAverage U A b +
        fourFactorFirst (cmp98Eq118SourceFactors U A b)
          (cmp98Eq118SourceFactorVariations U A b) 0 -
        cmp98Eq120ExitAverage U A b := by
  simp only [fourFactorFirst, cmp98Eq120SourceFactors_zero,
    cmp98Eq120SourceFactors_one, cmp98Eq120SourceFactors_two,
    cmp98Eq120SourceFactors_three,
    cmp98Eq120SourceFactorVariations_zero,
    cmp98Eq120SourceFactorVariations_one,
    cmp98Eq120SourceFactorVariations_two,
    cmp98Eq120SourceFactorVariations_three]
  have hzeroE : (0 : ℝ) • (-cmp98Eq120EntranceAverage U A b) = 0 :=
    zero_smul ℝ _
  have hzeroX : (0 : ℝ) • (-cmp98Eq120ExitAverage U A b) = 0 :=
    zero_smul ℝ _
  rw [hzeroE, hzeroX, NormedSpace.exp_zero,
    cmp98Eq118SourceCurve_zero U A b]
  noncomm_ring

/-- Right-frame assembly of (119) plus the endpoint conjugations of (120). -/
def cmp98Eq120RightAssembledPhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq119RightFourSourcePhysicalVariation U A b +
    cmp98Eq119DirectCoarseTransportedVariation U A b +
      cmp98Eq120PhysicalEndpointCorrection U A b

/-- **Source-faithful derivative of CMP98 (120).**  The endpoint correction,
outer sign, four logarithmic sources and direct coarse term are all generated
internally from the literal based curve. -/
theorem deriv_cmp98Eq120SourceCurve_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    deriv (cmp98Eq120SourceCurve U A b) 0 =
      cmp98Eq120RightAssembledPhysicalVariation U A b := by
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
    intro x hx
    exact lt_of_le_of_lt (hthird x hx) (by norm_num)
  rw [(hasDerivAt_cmp98Eq120SourceCurve U A b hsmall).deriv,
    cmp98Eq120SourceFirstVariation_eq,
    cmp98Eq118SourceFirstVariation_eq]
  have hright := cmp98_fderiv_exp_mul_exp_neg_eq_gad_neg_apply
    (cmp98UbarLogAverage U b 0)
    (cmp98UbarLogAveragePhysicalVariation U A b)
  calc
    -cmp98Eq120EntranceAverage U A b +
          ((fderiv ℝ NormedSpace.exp (cmp98UbarLogAverage U b 0))
              (cmp98UbarLogAveragePhysicalVariation U A b) *
            NormedSpace.exp (-(cmp98UbarLogAverage U b 0)) +
            cmp98Eq119DirectCoarseTransportedVariation U A b) -
        cmp98Eq120ExitAverage U A b =
      -cmp98Eq120EntranceAverage U A b +
          (cmp98GAd (-(cmp98UbarLogAverage U b 0))
              (cmp98UbarLogAveragePhysicalVariation U A b) +
            cmp98Eq119DirectCoarseTransportedVariation U A b) -
        cmp98Eq120ExitAverage U A b := by
          exact congrArg
            (fun z => -cmp98Eq120EntranceAverage U A b +
              (z + cmp98Eq119DirectCoarseTransportedVariation U A b) -
                cmp98Eq120ExitAverage U A b) hright
    _ = cmp98Eq120RightAssembledPhysicalVariation U A b := by
      rw [← cmp98Eq119RightFourSourcePhysicalVariation_eq_logVariation
        U A b hthird]
      unfold cmp98Eq120RightAssembledPhysicalVariation
      rw [cmp98Eq120PhysicalEndpointCorrection_eq_neg_averages]
      abel

end

end YangMills.RG
