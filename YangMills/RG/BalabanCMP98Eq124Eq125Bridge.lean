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

/-- **CMP98 (121), the printed `1/i` convention.**  Repository Lie
coordinates are represented by skew-Hermitian matrices; the Hermitian
coordinate printed by Balaban is therefore represented here by `(1/i)Y`.
This definition records the visible normalization without presupposing any
later sign identification in (124). -/
def cmp98Eq121PrintedLieCoordMatrix (X : SUNLieCoord Nc) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  (Complex.I : ℂ)⁻¹ • cmp98LieCoordMatrix X

/-- The printed `1/i` factor is literally multiplication by `-i`. -/
theorem cmp98Eq121PrintedLieCoordMatrix_eq_neg_I_smul
    (X : SUNLieCoord Nc) :
    cmp98Eq121PrintedLieCoordMatrix X =
      (-Complex.I : ℂ) • cmp98LieCoordMatrix X := by
  have hI : (Complex.I : ℂ)⁻¹ = -Complex.I := RCLike.inv_I
  rw [cmp98Eq121PrintedLieCoordMatrix, hI]

/-- Multiplication back by `i` recovers the repository's skew-Hermitian
matrix coordinate exactly. -/
theorem Complex.I_smul_cmp98Eq121PrintedLieCoordMatrix
    (X : SUNLieCoord Nc) :
    (Complex.I : ℂ) • cmp98Eq121PrintedLieCoordMatrix X =
      cmp98LieCoordMatrix X := by
  rw [cmp98Eq121PrintedLieCoordMatrix, smul_smul]
  simp

/-- The `1/i`-normalized matrix is Hermitian, matching the convention in
CMP98 (121), while `cmp98LieCoordMatrix X` itself is skew-Hermitian. -/
theorem cmp98Eq121PrintedLieCoordMatrix_isHermitian
    (X : SUNLieCoord Nc) :
    (cmp98Eq121PrintedLieCoordMatrix X).IsHermitian := by
  change Matrix.conjTranspose (cmp98Eq121PrintedLieCoordMatrix X) =
    cmp98Eq121PrintedLieCoordMatrix X
  rw [cmp98Eq121PrintedLieCoordMatrix_eq_neg_I_smul,
    Matrix.conjTranspose_smul]
  have hskew : Matrix.conjTranspose (cmp98LieCoordMatrix X) =
      -cmp98LieCoordMatrix X := by
    exact (((suLieCoordIso Nc).symm X).property).1
  rw [hskew]
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

/-- Equation (125) in the exact Hermitian convention of (121).  The
repository matrix equality is normalized by the source's visible `1/i`;
no sign or imaginary-unit convention remains implicit. -/
theorem cmp98Eq121PrintedLieCoordMatrix_eq125MainAverageValue
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq121PrintedLieCoordMatrix
        (cmp98Eq125MainAverageValue (matrixSUNAdjointModel Nc) U A b) =
      (Complex.I : ℂ)⁻¹ •
        ((M : ℝ)⁻¹ •
          (((M : ℝ) ^ d)⁻¹ •
            ∑ x ∈ blockOf M N' b.1,
              cmp98Eq124MiddlePrefixRightVariation U A b x)) := by
  apply congrArg (((Complex.I : ℂ)⁻¹) • ·)
  exact cmp98LieCoordMatrix_eq125MainAverageValue_eq_inv_mul_middleAverage
    U A b

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

/-- Outer `g(-i ad y)` part of CMP98 (119), represented in the repository's
skew-Hermitian coordinate convention, applied to the literal *local*
four-source block average.  The coefficients `(-1)^n` in `cmp98GAd` already
account for the printed minus sign in the argument of Balaban's scalar `g`.
The direct coarse-bond term of (119) is added separately below. -/
def cmp98Eq124FourSourcePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98GAd (cmp98UbarLogAverage U b 0)
    (cmp98Eq124FourSourceGAdInvAverage U A b)

/-- One local source transported by the exact outer/local operator product
in the repository's physical right-trivialized frame.  The established
frame-removal identities convert this to Balaban's displayed
`g(-i ad y) g(-i ad y_x)⁻¹` form under the printed logarithmic radius. -/
def cmp98Eq119OuterLocalTransport
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (H : Matrix (Fin Nc) (Fin Nc) ℂ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  let Y := nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)
  let D := fourFactorProduct (cmp98UbarContourFactors U A b x) 0
  cmp98GAd (cmp98UbarLogAverage U b 0)
    (cmp98GAdInv Y (Matrix.conjTranspose D * H * D))

/-- The physical-frame transport is exactly the sign-reversed unframed
local inverse dictated by `g⁻¹(-z)e^z = g⁻¹(z)`.  Both inverse certificates
are produced from Balaban's one-third local logarithmic radius. -/
theorem cmp98Eq119OuterLocalTransport_eq_signReversed
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (H : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hthird : ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98Eq119OuterLocalTransport U A b x H =
      cmp98GAd (cmp98UbarLogAverage U b 0)
        (cmp98GAdInv
          (-(nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))) H) := by
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
  unfold cmp98Eq119OuterLocalTransport
  change cmp98GAd (cmp98UbarLogAverage U b 0)
      (cmp98GAdInv Y (Matrix.conjTranspose D * H * D)) = _
  rw [← hDneg, ← hD,
    cmp98GAdInv_apply_exp_neg_ad_eq_gadInv_neg
      Y H hGsmall hGsmallNeg]

/-- Entrance `operator - 1` correction in the exact physical frame. -/
def cmp98Eq119EntranceOperatorMinusId
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq119OuterLocalTransport U A b x
      (cmp98Eq124EntrancePrefixRightVariation U A b x) -
    cmp98Eq124EntrancePrefixRightVariation U A b x

/-- Straight-line `operator - 1` correction in the exact physical frame. -/
def cmp98Eq119MiddleOperatorMinusId
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq119OuterLocalTransport U A b x
      (cmp98Eq124MiddlePrefixRightVariation U A b x) -
    cmp98Eq124MiddlePrefixRightVariation U A b x

/-- Physical-frame regrouping of the local averaged part of `Q'` in (119).
The two raw source terms are displayed separately from their exact
`operator - 1` corrections.  CMP98 (120) later cancels the raw entrance
term and changes the endpoint/coarse contribution; that additional physical
conjugation is deliberately not folded into this definition. -/
def cmp98Eq119RegroupedFourSourcePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      (cmp98Eq124EntrancePrefixRightVariation U A b x +
        cmp98Eq124MiddlePrefixRightVariation U A b x +
        cmp98Eq119EntranceOperatorMinusId U A b x +
        cmp98Eq119MiddleOperatorMinusId U A b x +
        cmp98Eq119OuterLocalTransport U A b x
          (cmp98Eq124ExitPrefixRightVariation U A b x) +
        cmp98Eq119OuterLocalTransport U A b x
          (cmp98Eq124CoarsePrefixRightVariation U A b x))

/-- **Exact operator-minus-identity decomposition of the local part of
CMP98 (119).**  This is the algebraic regrouping needed before adjoining the
direct coarse term and consuming the endpoint conjugations in (120).  No
estimate or arbitrary correction matrix is used. -/
theorem cmp98Eq124FourSourcePhysicalVariation_eq_eq119Regrouped
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq124FourSourcePhysicalVariation U A b =
      cmp98Eq119RegroupedFourSourcePhysicalVariation U A b := by
  unfold cmp98Eq124FourSourcePhysicalVariation
    cmp98Eq124FourSourceGAdInvAverage
    cmp98Eq119RegroupedFourSourcePhysicalVariation
  rw [map_smul]
  apply congrArg (((M : ℝ) ^ d)⁻¹ • ·)
  calc
    cmp98GAd (cmp98UbarLogAverage U b 0)
        (∑ x ∈ blockOf M N' b.1,
          cmp98Eq124LocalFourSourceGAdInvVariation U A b x) =
      ∑ x ∈ blockOf M N' b.1,
        cmp98GAd (cmp98UbarLogAverage U b 0)
          (cmp98Eq124LocalFourSourceGAdInvVariation U A b x) := by
        induction blockOf M N' b.1 using Finset.induction_on with
        | empty => exact (cmp98GAd (cmp98UbarLogAverage U b 0)).map_zero
        | @insert x s hx ih =>
            simp only [Finset.sum_insert, hx, not_false_eq_true, map_add]
            rw [ih]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [cmp98Eq124LocalFourSourceGAdInvVariation, map_add,
        cmp98Eq119OuterLocalTransport, cmp98Eq119EntranceOperatorMinusId,
        cmp98Eq119MiddleOperatorMinusId]
      abel

/-- Every edge of the literal coarse basepoint-to-basepoint path is
positively oriented. -/
theorem cmp98SourceCoarseBondPath_edges_pos
    (b : PhysicalBond d N') :
    ∀ e ∈ cmp98SourceCoarseBondPath (Nc := Nc) (M := M) b,
      e.sign = true := by
  exact cmp99StraightPositivePath_edges_pos
    (Nc := Nc) (blockBasepoint M N' b.1) b.2 M

/-- Literal right-trivialized variation `(R₀,c₋ A)(c)` of the coarse
straight path in CMP98 (119). -/
def cmp98Eq119CoarseRightVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98ContourFirstVariation U A
      (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 *
    Matrix.conjTranspose
      (cmp98ContourMatrixCurve U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)

/-- The coarse variation is exactly the ordered positive-contour generator
sum; it is not an independently supplied matrix. -/
theorem cmp98Eq119CoarseRightVariation_eq_positiveContourRightVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq119CoarseRightVariation U A b =
      cmp98PositiveContourRightVariation U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) := by
  unfold cmp98Eq119CoarseRightVariation
  exact cmp98ContourFirstVariation_mul_conjTranspose_eq_rightVariation
    U A (cmp98SourceCoarseBondPath (Nc := Nc) b)
      (cmp98SourceCoarseBondPath_edges_pos (Nc := Nc) b)

/-- The direct `R(e^{iY})(R₀,c₋ A)(c)` term printed at the end of CMP98
(119), using literal exponential conjugation by the block logarithm. -/
def cmp98Eq119DirectCoarseTransportedVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  NormedSpace.exp (cmp98UbarLogAverage U b 0) *
    cmp98Eq119CoarseRightVariation U A b *
    NormedSpace.exp (-(cmp98UbarLogAverage U b 0))

/-- Complete physical variation of `Q'` in (119): the local averaged
four-contour term plus the literal transported coarse-bond contribution. -/
def cmp98Eq119CompletePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq124FourSourcePhysicalVariation U A b +
    cmp98Eq119DirectCoarseTransportedVariation U A b

/-- The complete (119) variation in its exact local-regrouped form. -/
theorem cmp98Eq119CompletePhysicalVariation_eq_regrouped_add_direct
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq119CompletePhysicalVariation U A b =
      cmp98Eq119RegroupedFourSourcePhysicalVariation U A b +
        cmp98Eq119DirectCoarseTransportedVariation U A b := by
  unfold cmp98Eq119CompletePhysicalVariation
  rw [cmp98Eq124FourSourcePhysicalVariation_eq_eq119Regrouped]

/-- Literal endpoint contribution displayed in CMP98 (120): subtraction of
the entrance right variation and of the oriented return-contour right
variation.  The latter already carries the source orientation through the
physical path `Γ₃ : x' → c₊`. -/
def cmp98Eq120PhysicalEndpointCorrection
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      (0 - cmp98Eq124EntrancePrefixRightVariation U A b x -
        cmp98Eq124ExitPrefixRightVariation U A b x)

/-- Source-level assembly of the linear coordinate after the endpoint
conjugations in (120).  A later theorem must identify this assembly with the
derivative of the literal full nonlinear conjugated background; the present
definition does not hide that remaining obligation. -/
def cmp98Eq120AssembledPhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq119CompletePhysicalVariation U A b +
    cmp98Eq120PhysicalEndpointCorrection U A b

/-- The four printed groups of CMP98 (124), still in exact physical frames:
main straight term; entrance and straight `operator - 1` corrections; return
contour correction; and the local/direct coarse pair. -/
def cmp98Eq124PrintedFourLinePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
      ∑ x ∈ blockOf M N' b.1,
        (cmp98Eq124MiddlePrefixRightVariation U A b x +
          cmp98Eq119EntranceOperatorMinusId U A b x +
          cmp98Eq119MiddleOperatorMinusId U A b x +
          (cmp98Eq119OuterLocalTransport U A b x
              (cmp98Eq124ExitPrefixRightVariation U A b x) -
            cmp98Eq124ExitPrefixRightVariation U A b x) +
          cmp98Eq119OuterLocalTransport U A b x
            (cmp98Eq124CoarsePrefixRightVariation U A b x)) +
    cmp98Eq119DirectCoarseTransportedVariation U A b

/-- **Exact algebraic passage (119)+(120) → the four lines of (124).**
Every summand is a literal contour variation.  This theorem performs only
the source's cancellations and `operator - 1` regrouping; it does not assume
the desired estimate or rename the remaining nonlinear conjugation bridge. -/
theorem cmp98Eq120AssembledPhysicalVariation_eq_eq124PrintedFourLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq120AssembledPhysicalVariation U A b =
      cmp98Eq124PrintedFourLinePhysicalVariation U A b := by
  rw [cmp98Eq120AssembledPhysicalVariation,
    cmp98Eq119CompletePhysicalVariation_eq_regrouped_add_direct]
  unfold cmp98Eq119RegroupedFourSourcePhysicalVariation
    cmp98Eq120PhysicalEndpointCorrection
    cmp98Eq124PrintedFourLinePhysicalVariation
  let w : ℝ := ((M : ℝ) ^ d)⁻¹
  let direct : Matrix (Fin Nc) (Fin Nc) ℂ :=
    cmp98Eq119DirectCoarseTransportedVariation U A b
  let localTerm : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ := fun x =>
    cmp98Eq124EntrancePrefixRightVariation U A b x +
      cmp98Eq124MiddlePrefixRightVariation U A b x +
      cmp98Eq119EntranceOperatorMinusId U A b x +
      cmp98Eq119MiddleOperatorMinusId U A b x +
      cmp98Eq119OuterLocalTransport U A b x
        (cmp98Eq124ExitPrefixRightVariation U A b x) +
      cmp98Eq119OuterLocalTransport U A b x
        (cmp98Eq124CoarsePrefixRightVariation U A b x)
  let endpoint : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ := fun x =>
    0 - cmp98Eq124EntrancePrefixRightVariation U A b x -
      cmp98Eq124ExitPrefixRightVariation U A b x
  let printed : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ := fun x =>
    cmp98Eq124MiddlePrefixRightVariation U A b x +
      cmp98Eq119EntranceOperatorMinusId U A b x +
      cmp98Eq119MiddleOperatorMinusId U A b x +
      (cmp98Eq119OuterLocalTransport U A b x
          (cmp98Eq124ExitPrefixRightVariation U A b x) -
        cmp98Eq124ExitPrefixRightVariation U A b x) +
      cmp98Eq119OuterLocalTransport U A b x
        (cmp98Eq124CoarsePrefixRightVariation U A b x)
  change w • (∑ x ∈ blockOf M N' b.1, localTerm x) + direct +
      w • (∑ x ∈ blockOf M N' b.1, endpoint x) =
    w • (∑ x ∈ blockOf M N' b.1, printed x) + direct
  have hpoint : ∀ x : FinBox d (M * N'),
      localTerm x + endpoint x = printed x := by
    intro x
    dsimp only [localTerm, endpoint, printed]
    abel
  have hsum :
      (∑ x ∈ blockOf M N' b.1, localTerm x) +
          (∑ x ∈ blockOf M N' b.1, endpoint x) =
        ∑ x ∈ blockOf M N' b.1, printed x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    exact hpoint x
  have hsmul :
      w • ((∑ x ∈ blockOf M N' b.1, localTerm x) +
          (∑ x ∈ blockOf M N' b.1, endpoint x)) =
        w • (∑ x ∈ blockOf M N' b.1, localTerm x) +
          w • (∑ x ∈ blockOf M N' b.1, endpoint x) := by
    ext i j
    simp [mul_add]
  calc
    w • (∑ x ∈ blockOf M N' b.1, localTerm x) + direct +
        w • (∑ x ∈ blockOf M N' b.1, endpoint x) =
      w • (∑ x ∈ blockOf M N' b.1, localTerm x) +
          w • (∑ x ∈ blockOf M N' b.1, endpoint x) + direct := by
            abel
    _ =
      w • ((∑ x ∈ blockOf M N' b.1, localTerm x) +
        (∑ x ∈ blockOf M N' b.1, endpoint x)) + direct := by
          exact congrArg (fun z => z + direct) hsmul.symm
    _ = w • (∑ x ∈ blockOf M N' b.1, printed x) + direct := by
      rw [hsum]

/-- **Four-source form of the CMP98 (119) building block for (124).**  Under
the single geometric local radius, the left-trivialized nonlinear block
variation is the outer `g(-i ad y)` applied to the exact entrance, middle,
exit and coarse sources.  The endpoint conjugations of (120) are a separate
subsequent dictionary obligation. -/
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
