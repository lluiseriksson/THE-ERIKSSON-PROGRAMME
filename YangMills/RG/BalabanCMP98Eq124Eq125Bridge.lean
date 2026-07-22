/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq125OrderedDictionary
import YangMills.RG.BalabanCMP98FourContourRightTrivialization
import YangMills.RG.BalabanCMP98GAdConjugation

/-!
# Source bridge between CMP98 equations (124) and (125)

The four-contour calculation names the physical middle source before any
coordinate conversion.  Equation (125) describes the same source as a
transported Lie-coordinate line sum.  This module proves their literal
pointwise equality and keeps the extra inverse block length visible.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq124Eq125BridgeMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The named middle source term in the four-contour decomposition is
literally the matrix realization of the transported line sum printed in
CMP98 (125). -/
theorem cmp98Eq124MiddlePrefixRightVariation_eq_eq125TransportedLineSum
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' b.1}) :
    cmp98Eq124MiddlePrefixRightVariation U A b x.1 =
      cmp98LieCoordMatrix
        (cmp98Eq125TransportedLineSum (matrixSUNAdjointModel Nc)
          U A b.1 x b.2) := by
  rw [cmp98LieCoordMatrix_eq125TransportedLineSum_eq_rightVariation]
  unfold cmp98Eq124MiddlePrefixRightVariation cmp98UbarContourFactors
    cmp98UbarContourFactorVariations
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    cmp98ContourMatrixCurve_zero_eq_wilsonLine,
    cmp98Gamma1PrefixHolonomy]

/-- **Normalized block bridge.**  The main operator of CMP98 (125) is one
additional inverse block length times the `M⁻ᵈ` average of the literal
middle source extracted from (124). -/
theorem cmp98LieCoordMatrix_eq125MainAverageValue_eq_inv_mul_middleAverage
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98LieCoordMatrix
        (cmp98Eq125MainAverageValue (matrixSUNAdjointModel Nc) U A b) =
      (M : ℝ)⁻¹ •
        (((M : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf M N' b.1,
            cmp98Eq124MiddlePrefixRightVariation U A b x) := by
  rw [cmp98LieCoordMatrix_eq125MainAverageValue_normalized]
  apply congrArg (((M : ℝ)⁻¹) • ·)
  apply congrArg ((((M : ℝ) ^ d)⁻¹) • ·)
  rw [Finset.sum_subtype (blockOf M N' b.1) (fun _ => Iff.rfl)
    (fun x => cmp98Eq124MiddlePrefixRightVariation U A b x)]
  apply Finset.sum_congr rfl
  intro x _hx
  symm
  rw [cmp98Eq124MiddlePrefixRightVariation_eq_eq125TransportedLineSum
    U A b x]
  exact cmp98LieCoordMatrix_eq125TransportedLineSum_eq_rightVariation
    U A b x

/-- Sum of the four physical contour sources after the exact local
`g(ad y_x)⁻¹` operation. -/
def cmp98Eq124LocalFourSourceGAdInvVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  let Y := nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)
  let D := fourFactorProduct (cmp98UbarContourFactors U A b x) 0
  cmp98GAdInv Y (Matrix.conjTranspose D *
      cmp98Eq124EntrancePrefixRightVariation U A b x * D) +
    cmp98GAdInv Y (Matrix.conjTranspose D *
      cmp98Eq124MiddlePrefixRightVariation U A b x * D) +
    cmp98GAdInv Y (Matrix.conjTranspose D *
      cmp98Eq124ExitPrefixRightVariation U A b x * D) +
    cmp98GAdInv Y (Matrix.conjTranspose D *
      cmp98Eq124CoarsePrefixRightVariation U A b x * D)

/-- The four physical contour sources after the local inverse, but before
the exact change from the right-trivialized frame to the local left frame.
This is the source-facing form needed to isolate the `operator - 1`
corrections printed in CMP98 (124). -/
def cmp98Eq124LocalUnframedFourSourceGAdInvVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  let Y := nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)
  cmp98GAdInv Y (cmp98Eq124EntrancePrefixRightVariation U A b x) +
    cmp98GAdInv Y (cmp98Eq124MiddlePrefixRightVariation U A b x) +
    cmp98GAdInv Y (cmp98Eq124ExitPrefixRightVariation U A b x) +
    cmp98GAdInv Y (cmp98Eq124CoarsePrefixRightVariation U A b x)

/-- The four physical contour sources in the sign-reversed local inverse
frame printed in CMP98 (124).  This is not a new source package: the
following theorem derives it from the literal contour derivative using
`g⁻¹(-z)e^z = g⁻¹(z)`. -/
def cmp98Eq124LocalSignReversedFourSourceGAdInvVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  let Y := nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)
  cmp98GAdInv (-Y) (cmp98Eq124EntrancePrefixRightVariation U A b x) +
    cmp98GAdInv (-Y) (cmp98Eq124MiddlePrefixRightVariation U A b x) +
    cmp98GAdInv (-Y) (cmp98Eq124ExitPrefixRightVariation U A b x) +
    cmp98GAdInv (-Y) (cmp98Eq124CoarsePrefixRightVariation U A b x)

/-- **Exact left/right-frame dictionary for (124).**  The conjugations in
the local logarithmic derivative are not extra source terms: covariance of
`g(ad Y)⁻¹` factors them into one common `exp (-Y)`/`exp Y` pair around the
four unframed physical sources. -/
theorem cmp98Eq124LocalFourSourceGAdInvVariation_eq_exp_conj_unframed
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hthird : ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98Eq124LocalFourSourceGAdInvVariation U A b x =
      let Y := nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)
      NormedSpace.exp (-Y) *
        cmp98Eq124LocalUnframedFourSourceGAdInvVariation U A b x *
        NormedSpace.exp Y := by
  let Z := cmp98UbarAmbientDeviationMatrix U b x 0
  let Y := nearLog Z
  let D := fourFactorProduct (cmp98UbarContourFactors U A b x) 0
  have hZsmall : ‖Z‖ < 1 := lt_of_le_of_lt hthird (by norm_num)
  have hYhalf : ‖Y‖ ≤ 1 / 2 :=
    norm_nearLog_le_half_of_norm_le_third hthird
  have hGsmall :=
    norm_cmp98GAd_sub_id_lt_one_of_norm_le_half Y hYhalf
  have hD : NormedSpace.exp Y = D := by
    dsimp only [Y, Z, D]
    rw [exp_nearLog_eq_one_add hZsmall]
    have hline := cmp98UbarAmbientDeviationMatrix_line_eq_deviationCurve
      U A b x 0
    have hzero : (0 : ℝ) • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A) = 0 := zero_smul ℝ _
    rw [hzero] at hline
    change Z = D - 1 at hline
    rw [hline]
    abel
  have hDneg : NormedSpace.exp (-Y) = Matrix.conjTranspose D := by
    dsimp only [Y, Z, D]
    exact cmp98ExpNegNearLogDeviation_eq_productConjTranspose
      U A b x hZsmall
  dsimp only [cmp98Eq124LocalFourSourceGAdInvVariation,
    cmp98Eq124LocalUnframedFourSourceGAdInvVariation]
  change
    cmp98GAdInv Y (Matrix.conjTranspose D *
        cmp98Eq124EntrancePrefixRightVariation U A b x * D) +
      cmp98GAdInv Y (Matrix.conjTranspose D *
        cmp98Eq124MiddlePrefixRightVariation U A b x * D) +
      cmp98GAdInv Y (Matrix.conjTranspose D *
        cmp98Eq124ExitPrefixRightVariation U A b x * D) +
      cmp98GAdInv Y (Matrix.conjTranspose D *
        cmp98Eq124CoarsePrefixRightVariation U A b x * D) =
      NormedSpace.exp (-Y) *
        (cmp98GAdInv Y (cmp98Eq124EntrancePrefixRightVariation U A b x) +
          cmp98GAdInv Y (cmp98Eq124MiddlePrefixRightVariation U A b x) +
          cmp98GAdInv Y (cmp98Eq124ExitPrefixRightVariation U A b x) +
          cmp98GAdInv Y (cmp98Eq124CoarsePrefixRightVariation U A b x)) *
        NormedSpace.exp Y
  rw [← hDneg, ← hD]
  simp_rw [cmp98GAdInv_apply_exp_conjugation Y _ hGsmall]
  noncomm_ring

/-- **Exact sign-reversed inverse dictionary for CMP98 (124).**  The
conjugated local four-contour derivative is literally the sum obtained by
applying `g(ad (-Y))⁻¹` to the four unframed physical sources.  Both
Neumann contractions are derived from the printed one-third logarithmic
radius. -/
theorem cmp98Eq124LocalFourSourceGAdInvVariation_eq_signReversed
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hthird : ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98Eq124LocalFourSourceGAdInvVariation U A b x =
      cmp98Eq124LocalSignReversedFourSourceGAdInvVariation U A b x := by
  let Z := cmp98UbarAmbientDeviationMatrix U b x 0
  let Y := nearLog Z
  let D := fourFactorProduct (cmp98UbarContourFactors U A b x) 0
  have hZsmall : ‖Z‖ < 1 := lt_of_le_of_lt hthird (by norm_num)
  have hYhalf : ‖Y‖ ≤ 1 / 2 :=
    norm_nearLog_le_half_of_norm_le_third hthird
  have hYnegHalf : ‖-Y‖ ≤ 1 / 2 := by
    simpa only [norm_neg] using hYhalf
  have hGsmall :=
    norm_cmp98GAd_sub_id_lt_one_of_norm_le_half Y hYhalf
  have hGsmallNeg :=
    norm_cmp98GAd_sub_id_lt_one_of_norm_le_half (-Y) hYnegHalf
  have hD : NormedSpace.exp Y = D := by
    dsimp only [Y, Z, D]
    rw [exp_nearLog_eq_one_add hZsmall]
    have hline := cmp98UbarAmbientDeviationMatrix_line_eq_deviationCurve
      U A b x 0
    have hzero : (0 : ℝ) • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A) = 0 := zero_smul ℝ _
    rw [hzero] at hline
    change Z = D - 1 at hline
    rw [hline]
    abel
  have hDneg : NormedSpace.exp (-Y) = Matrix.conjTranspose D := by
    dsimp only [Y, Z, D]
    exact cmp98ExpNegNearLogDeviation_eq_productConjTranspose
      U A b x hZsmall
  dsimp only [cmp98Eq124LocalFourSourceGAdInvVariation,
    cmp98Eq124LocalSignReversedFourSourceGAdInvVariation]
  change
    cmp98GAdInv Y (Matrix.conjTranspose D *
        cmp98Eq124EntrancePrefixRightVariation U A b x * D) +
      cmp98GAdInv Y (Matrix.conjTranspose D *
        cmp98Eq124MiddlePrefixRightVariation U A b x * D) +
      cmp98GAdInv Y (Matrix.conjTranspose D *
        cmp98Eq124ExitPrefixRightVariation U A b x * D) +
      cmp98GAdInv Y (Matrix.conjTranspose D *
        cmp98Eq124CoarsePrefixRightVariation U A b x * D) =
    cmp98GAdInv (-Y) (cmp98Eq124EntrancePrefixRightVariation U A b x) +
      cmp98GAdInv (-Y) (cmp98Eq124MiddlePrefixRightVariation U A b x) +
      cmp98GAdInv (-Y) (cmp98Eq124ExitPrefixRightVariation U A b x) +
      cmp98GAdInv (-Y) (cmp98Eq124CoarsePrefixRightVariation U A b x)
  rw [← hDneg, ← hD]
  simp_rw [cmp98GAdInv_apply_exp_neg_ad_eq_gadInv_neg
    Y _ hGsmall hGsmallNeg]

/-- The local logarithmic derivative is exactly the four-source expression
at Balaban's geometric radius. -/
theorem cmp98LocalLogVariation_eq_fourSourceGAdInv_of_norm_le_third
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hthird : ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    (∑' n : ℕ, nearLogTermFDeriv
        (cmp98UbarAmbientDeviationMatrix U b x 0) n)
        (cmp98UbarDeviationFirstVariation U A b x 0) =
      cmp98Eq124LocalFourSourceGAdInvVariation U A b x := by
  have hsmall : ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 :=
    lt_of_le_of_lt hthird (by norm_num)
  calc
    (∑' n : ℕ, nearLogTermFDeriv
        (cmp98UbarAmbientDeviationMatrix U b x 0) n)
        (cmp98UbarDeviationFirstVariation U A b x 0) =
      cmp98GAdInv
        (nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))
        (NormedSpace.exp
            (-(nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))) *
          cmp98UbarDeviationFirstVariation U A b x 0) :=
      nearLog_fderiv_apply_eq_cmp98GAdInv_of_norm_le_third hthird _
    _ = cmp98Eq124LocalFourSourceGAdInvVariation U A b x := by
      exact cmp98GAdInv_localPhysicalVariation_eq_sum_fourSourceTerms
        U A b x hsmall

/-- Literal `M⁻ᵈ` block average of the four local source contributions. -/
def cmp98Eq124FourSourceGAdInvAverage
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      cmp98Eq124LocalFourSourceGAdInvVariation U A b x

/-- The complete physical logarithmic variation is the four-source block
average, with no arbitrary correction matrix left. -/
theorem cmp98UbarLogAveragePhysicalVariation_eq_fourSourceGAdInvAverage
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98UbarLogAveragePhysicalVariation U A b =
      cmp98Eq124FourSourceGAdInvAverage U A b := by
  unfold cmp98UbarLogAveragePhysicalVariation
    cmp98Eq124FourSourceGAdInvAverage
  apply congrArg (((M : ℝ) ^ d)⁻¹ • ·)
  apply Finset.sum_congr rfl
  intro x hx
  exact cmp98LocalLogVariation_eq_fourSourceGAdInv_of_norm_le_third
    U A b x (hthird x hx)

/-- Outer `g(ad y)` applied to the literal four-source block average. -/
def cmp98Eq124FourSourcePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98GAd (cmp98UbarLogAverage U b 0)
    (cmp98Eq124FourSourceGAdInvAverage U A b)

/-- **Four-source form of CMP98 (124).**  Under the single geometric local
radius, the left-trivialized nonlinear block variation is the outer
`g(ad y)` applied to the exact entrance, middle, exit and coarse sources. -/
theorem cmp98Eq124_leftTrivialized_physicalVariation_eq_fourSources
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    NormedSpace.exp (-(cmp98UbarLogAverage U b 0)) *
        fderiv ℝ (cmp98UbarExpAverage U b) 0
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) =
      cmp98Eq124FourSourcePhysicalVariation U A b := by
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
    intro x hx
    exact lt_of_le_of_lt (hthird x hx) (by norm_num)
  rw [cmp98Eq124_leftTrivialized_physicalVariation_eq_gad U A b hsmall]
  unfold cmp98Eq124GAdPhysicalVariation
    cmp98Eq124FourSourcePhysicalVariation
  rw [cmp98UbarLogAveragePhysicalVariation_eq_fourSourceGAdInvAverage
    U A b hthird]

/-- Source-instantiated four-source endpoint: uniform fine-link smallness
and the printed path-radius budget produce the complete local and outer
`g(ad)` structure of (124). -/
theorem cmp98Eq124_leftTrivialized_physicalVariation_eq_fourSources_of_sourceFineSmall
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (hradius : cmp99SourceUbarFineDeviationRadius d M epsilonFine ≤ 1 / 3) :
    NormedSpace.exp (-(cmp98UbarLogAverage U b 0)) *
        fderiv ℝ (cmp98UbarExpAverage U b) 0
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) =
      cmp98Eq124FourSourcePhysicalVariation U A b := by
  apply cmp98Eq124_leftTrivialized_physicalVariation_eq_fourSources
  intro x hx
  exact (norm_cmp98UbarAmbientDeviationMatrix_zero_le_fineRadius
    hd hM U epsilonFine epsilonFine_nonneg fine_small b x hx).trans hradius

end

end YangMills.RG
