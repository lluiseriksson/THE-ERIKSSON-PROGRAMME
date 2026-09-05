/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116InteractingCombesThomas
import YangMills.RG.BalabanCMP116Eq214FlatDeltaBound
import YangMills.RG.BalabanCMP96ConstraintNorm
import YangMills.RG.BalabanCMP99SourceCoarseCovariance

/-!
# An unprojected auxiliary realization of the CMP99 equation-(3.126) formula

CMP99 equation (3.126), printed p. 420, identifies the one-cochain
background-field minimizer algebraically as

`H B = G Q^* (Q G Q^*)^-1 B`.

This is distinct from the gauge-parameter operator `H'` in equation (3.163),
whose middle contains `G'^2`.  The module below instantiates the algebraic
formula using the existing CMP116 interacting precision with the
*unprojected* gauge-fixing mass `D D^*`.  Its block constraint is the literal
CMP96/CMP116 map, and the sparse pivot insertion generates the adjoint lower
bound needed to invert `Q G Q^*` without a surjectivity hypothesis.

The terminal theorem proves `Q H = 1` for this auxiliary precision.  It is not
yet the complete source realization of (3.126): CMP99 equation (3.122) uses
`Delta'_pi + Delta^eta + D R D^* + Q^* a Q`, with `R` from equation (3.25),
and the reduction to (3.126) additionally uses equation (3.124)
`R D^* G Q^* = 0`.  Neither the projected mass, `Delta'_pi`, nor (3.124) is
claimed here.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

set_option maxRecDepth 4000

variable {d L N' Nc : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]

/-- A volume-independent upper bound for the complete interacting precision
used in the source formula (3.126). -/
def cmp99SourceEq3126PhysicalPrecisionUpperBound
    (d L Nc : ℕ) (a ε : ℝ) : ℝ :=
  cmp116Eq214FlatDeltaNormBound d L a +
    cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε

theorem cmp99SourceEq3126PhysicalPrecisionUpperBound_pos
    (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 < cmp99SourceEq3126PhysicalPrecisionUpperBound d L Nc a ε := by
  unfold cmp99SourceEq3126PhysicalPrecisionUpperBound
  have hd : (0 : ℝ) < d := by
    exact_mod_cast (NeZero.pos d)
  have hL : (0 : ℝ) < L := by
    exact_mod_cast (NeZero.pos L)
  have hflat : 0 < cmp116Eq214FlatDeltaNormBound d L a := by
    unfold cmp116Eq214FlatDeltaNormBound
    have hleft :
        0 < (((4 * d : ℕ) : ℝ) ^ 2 + (2 : ℝ) ^ 2) +
          |a| * (L : ℝ) ^ 2 := by positivity
    have hcountNat : 0 < (2 * (3 * L + 1)) ^ d * d :=
      Nat.mul_pos (pow_pos (by omega) _) (NeZero.pos d)
    have hcount :
        (0 : ℝ) < (((2 * (3 * L + 1)) ^ d * d : ℕ) : ℝ) := by
      exact_mod_cast hcountNat
    exact mul_pos hleft hcount
  have hdef :
      0 ≤ cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε := by
    unfold cmp116ConcreteInteractingWilsonGaugeDefectBudget
    unfold cmp116InteractingWilsonGaugeDefectBudget
    unfold cmp116WilsonHessianDefectRate cmp116GaugeFixingMassDefectRate
    positivity
  positivity

/-- Uniform operator norm of the complete interacting precision. -/
theorem norm_interactingPhysicalBasePrecisionCLM_le_sourceEq3126
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε) :
    ‖interactingPhysicalBasePrecisionCLM U a‖ ≤
      cmp99SourceEq3126PhysicalPrecisionUpperBound d L Nc a ε := by
  rw [interactingPhysicalBasePrecisionCLM,
    interactingWilsonGaugeBasePrecisionCLM_eq_flat_add_defect]
  calc
    ‖gaugeFixedBasePrecisionCLM
          (flatGaugeHodgeK0CLM d (L * N') Nc (matrixSUNAdjointModel Nc))
          (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a +
        interactingWilsonGaugeDefectCLM U‖ ≤
        ‖gaugeFixedBasePrecisionCLM
          (flatGaugeHodgeK0CLM d (L * N') Nc (matrixSUNAdjointModel Nc))
          (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a‖ +
          ‖interactingWilsonGaugeDefectCLM U‖ := norm_add_le _ _
    _ ≤ cmp116Eq214FlatDeltaNormBound d L a +
        cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε :=
      add_le_add
        (norm_flatCMP116DeltaCLM_le (matrixSUNAdjointModel Nc) a)
        (norm_interactingWilsonGaugeDefectCLM_le_of_wilson U hε hsmall)
    _ = cmp99SourceEq3126PhysicalPrecisionUpperBound d L Nc a ε := rfl

/-- Symmetry of the complete Wilson plus gauge Hodge operator. -/
theorem interactingWilsonGaugeHodgeCLM_isSymmetric
    (U : PhysicalGaugeBackground d (L * N') Nc) :
    (interactingWilsonGaugeHodgeCLM U).IsSymmetric := by
  let K := interactingWilsonGaugeHodgeCLM U
  have hAdj : K.adjoint = K := by
    simp [K, interactingWilsonGaugeHodgeCLM,
      physicalWilsonHessianCLM_adjoint_eq, gaugeFixingMassCLM,
      ContinuousLinearMap.adjoint_comp]
  exact (ContinuousLinearMap.eq_adjoint_iff K K).mp hAdj.symm

/-- Symmetry of the complete interacting precision. -/
theorem interactingPhysicalBasePrecisionCLM_isSymmetric
    (U : PhysicalGaugeBackground d (L * N') Nc) (a : ℝ) :
    (interactingPhysicalBasePrecisionCLM U a).IsSymmetric := by
  change
    (cmp99SourceGaugePrecision
      (interactingWilsonGaugeHodgeCLM U)
      (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a).IsSymmetric
  exact cmp99SourceGaugePrecision_isSymmetric _ _ _
    (interactingWilsonGaugeHodgeCLM_isSymmetric U)

/-- The sparse physical right inverse of `Q` produces the exact
volume-independent lower bound for `Q^*`. -/
theorem inv_pow_mul_norm_le_norm_flatBlockConstraintQCLM_adjoint
    (eta : CoarsePhysicalOneCochain d N' Nc) :
    ((L : ℝ) ^ (d - 1))⁻¹ * ‖eta‖ ≤
      ‖(flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').adjoint eta‖ := by
  let Q := flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
  let E := cmp96ConstraintPivotInsertionCLM
    (d := d) (L := L) (N' := N') (Nc := Nc)
  let scale : ℝ := (L : ℝ) ^ (d - 1)
  have hscale : 0 < scale := by
    dsimp [scale]
    have hL : (0 : ℝ) < L := by
      exact_mod_cast (NeZero.pos L)
    exact pow_pos hL _
  by_cases heta : eta = 0
  · simp [heta]
  have hetaNorm : 0 < ‖eta‖ := norm_pos_iff.mpr heta
  have hQE : Q.comp E = ContinuousLinearMap.id ℝ _ := by
    exact flatBlockConstraint_comp_pivotInsertionCLM
  have hQEval : Q (E eta) = eta := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun T => T eta) hQE
  have hinner : ‖eta‖ ^ 2 = inner ℝ (Q.adjoint eta) (E eta) := by
    calc
      ‖eta‖ ^ 2 = inner ℝ eta eta := (real_inner_self_eq_norm_sq eta).symm
      _ = inner ℝ eta (Q (E eta)) := by rw [hQEval]
      _ = inner ℝ (Q.adjoint eta) (E eta) := by
        rw [ContinuousLinearMap.adjoint_inner_left]
  have hcs : ‖eta‖ ^ 2 ≤ ‖Q.adjoint eta‖ * ‖E eta‖ := by
    rw [hinner]
    exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hEnorm : ‖E eta‖ = scale * ‖eta‖ := by
    change ‖cmp96ConstraintPivotInsertion (L := L) eta‖ = _
    exact norm_cmp96ConstraintPivotInsertion eta
  rw [hEnorm] at hcs
  have hcancel : ‖eta‖ ≤ scale * ‖Q.adjoint eta‖ := by
    have hmul : ‖eta‖ * ‖eta‖ ≤
        (scale * ‖Q.adjoint eta‖) * ‖eta‖ := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcs
    exact le_of_mul_le_mul_right hmul hetaNorm
  calc
    scale⁻¹ * ‖eta‖ ≤ scale⁻¹ * (scale * ‖Q.adjoint eta‖) :=
      mul_le_mul_of_nonneg_left hcancel (inv_nonneg.mpr hscale.le)
    _ = ‖Q.adjoint eta‖ := by field_simp

/-- Literal one-cochain middle `Q G Q^*` in CMP99 equation (3.126). -/
noncomputable def cmp99SourceEq3126PhysicalCoarseMiddle
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP) :
    CoarsePhysicalOneCochain d N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc :=
  let Q := flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
  let G := interactingPhysicalCovarianceCLM U ha hP hε hsmall hbudget
  Q.comp (G.comp Q.adjoint)

/-- Quadratic-form identity for the physical middle. -/
theorem inner_cmp99SourceEq3126PhysicalCoarseMiddle
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (eta : CoarsePhysicalOneCochain d N' Nc) :
    inner ℝ eta
        (cmp99SourceEq3126PhysicalCoarseMiddle U ha hP hε hsmall hbudget eta) =
      inner ℝ
        ((flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').adjoint eta)
        (interactingPhysicalCovarianceCLM U ha hP hε hsmall hbudget
          ((flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').adjoint eta)) := by
  rw [cmp99SourceEq3126PhysicalCoarseMiddle]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- The physical middle is coercive, with every constant generated from the
interacting precision and the literal right inverse of `Q`. -/
theorem isCoerciveCLM_cmp99SourceEq3126PhysicalCoarseMiddle
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP) :
    IsCoerciveCLM
      (cmp99SourceEq3126PhysicalCoarseMiddle U ha hP hε hsmall hbudget)
      ((min 1 a / CP -
          cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε) *
        (((L : ℝ) ^ (d - 1))⁻¹ /
          cmp99SourceEq3126PhysicalPrecisionUpperBound d L Nc a ε) ^ 2) := by
  let A := interactingPhysicalBasePrecisionCLM U a
  let G := interactingPhysicalCovarianceCLM U ha hP hε hsmall hbudget
  let Q := flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
  let c := min 1 a / CP -
    cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε
  let q := ((L : ℝ) ^ (d - 1))⁻¹
  let Lambda := cmp99SourceEq3126PhysicalPrecisionUpperBound d L Nc a ε
  have hc : 0 < c := sub_pos.mpr hbudget
  have hLambdaPos : 0 < Lambda :=
    cmp99SourceEq3126PhysicalPrecisionUpperBound_pos a hε
  have hA : IsCoerciveCLM A c :=
    isCoerciveCLM_interactingPhysicalBasePrecision U ha hP hε hsmall
  have hSymm : A.IsSymmetric :=
    interactingPhysicalBasePrecisionCLM_isSymmetric U a
  have hLambda : ‖A‖ ≤ Lambda :=
    norm_interactingPhysicalBasePrecisionCLM_le_sourceEq3126 U a hε hsmall
  have hQlower : ∀ eta : CoarsePhysicalOneCochain d N' Nc,
      q * ‖eta‖ ≤ ‖Q.adjoint eta‖ := by
    intro eta
    exact inv_pow_mul_norm_le_norm_flatBlockConstraintQCLM_adjoint eta
  intro eta
  let y := Q.adjoint eta
  let x := G y
  have hAx : A x = y := by
    dsimp [x, G, A]
    exact precision_apply_covarianceOfIsCoerciveCLM _ _ _ _
  have hinverse := norm_le_mul_norm_covarianceOfIsCoerciveCLM
    A hc hA hLambda y
  have hlower : (q / Lambda) * ‖eta‖ ≤ ‖x‖ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLambdaPos).2
    calc
      q * ‖eta‖ ≤ ‖y‖ := hQlower eta
      _ ≤ Lambda * ‖x‖ := hinverse
      _ = ‖x‖ * Lambda := mul_comm _ _
  have hnonneg : 0 ≤ (q / Lambda) * ‖eta‖ := by
    dsimp [q]
    positivity
  rw [inner_cmp99SourceEq3126PhysicalCoarseMiddle]
  change c * (q / Lambda) ^ 2 * ‖eta‖ ^ 2 ≤ inner ℝ y x
  have hcoer := hA x
  rw [hAx] at hcoer
  calc
    c * (q / Lambda) ^ 2 * ‖eta‖ ^ 2 =
        c * ((q / Lambda) * ‖eta‖) ^ 2 := by ring
    _ ≤ c * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hnonneg hlower 2) hc.le
    _ ≤ inner ℝ x y := hcoer
    _ = inner ℝ y x := real_inner_comm _ _

/-- The inverse of the physical middle in equation (3.126). -/
noncomputable def cmp99SourceEq3126PhysicalCoarseCovariance
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP) :
    CoarsePhysicalOneCochain d N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc :=
  covarianceOfIsCoerciveCLM
    (cmp99SourceEq3126PhysicalCoarseMiddle U ha hP hε hsmall hbudget)
    (mul_pos (sub_pos.mpr hbudget)
      (sq_pos_of_pos (div_pos
        (inv_pos.mpr (pow_pos (by exact_mod_cast NeZero.pos L) (d - 1)))
        (cmp99SourceEq3126PhysicalPrecisionUpperBound_pos a hε))))
    (isCoerciveCLM_cmp99SourceEq3126PhysicalCoarseMiddle
      U ha hP hε hsmall hbudget)

/-- The middle followed by its generated covariance is the identity. -/
theorem cmp99SourceEq3126PhysicalCoarseMiddle_comp_covariance
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP) :
    (cmp99SourceEq3126PhysicalCoarseMiddle U ha hP hε hsmall hbudget).comp
      (cmp99SourceEq3126PhysicalCoarseCovariance
        U ha hP hε hsmall hbudget) =
      ContinuousLinearMap.id ℝ (CoarsePhysicalOneCochain d N' Nc) := by
  exact precision_comp_covarianceOfIsCoerciveCLM _ _ _

/-- Auxiliary one-scale realization of the algebraic expression printed in
CMP99 equation (3.126), using the unprojected CMP116 precision. -/
noncomputable def cmp99SourceEq3126PhysicalH
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP) :
    CoarsePhysicalOneCochain d N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  let Q := flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
  let G := interactingPhysicalCovarianceCLM U ha hP hε hsmall hbudget
  let C := cmp99SourceEq3126PhysicalCoarseCovariance
    U ha hP hε hsmall hbudget
  G.comp (Q.adjoint.comp C)

/-- Exact block response `Q H = 1` for the auxiliary unprojected precision. -/
theorem flatBlockConstraint_comp_cmp99SourceEq3126PhysicalH_eq_id
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP) :
    (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').comp
      (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget) =
      ContinuousLinearMap.id ℝ (CoarsePhysicalOneCochain d N' Nc) := by
  change
    (cmp99SourceEq3126PhysicalCoarseMiddle U ha hP hε hsmall hbudget).comp
      (cmp99SourceEq3126PhysicalCoarseCovariance
        U ha hP hε hsmall hbudget) = _
  exact cmp99SourceEq3126PhysicalCoarseMiddle_comp_covariance
    U ha hP hε hsmall hbudget

end

end YangMills.RG
