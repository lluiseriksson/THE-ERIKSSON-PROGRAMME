/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalBackgroundCorrectionFixedPoint
import YangMills.RG.BalabanCMP102PhysicalBackgroundBaseBudget
import YangMills.RG.BalabanCMP102PhysicalUniformChartBudget

/-!
# Scalar source closure of the CMP102 physical fixed point

This module replaces the two remaining functional fields of the Banach
certificate—pointwise chart construction and self-mapping—by explicit scalar
source inequalities.  The resulting endpoint constructs every chart on the
ball and the correction self-bound internally.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The common source-sup envelope of all fields `A - H D` with `‖D‖ ≤ ρ`. -/
def cmp102PhysicalBackgroundBallSourceEnvelope
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : PhysicalGaugeOneCochain d (L * N') Nc)
    (ρ : ℝ) : ℝ :=
  cmp98SourceFieldSupNorm A +
    cmp99SourceEq3126PhysicalHSourceSupNorm
      U ha hP hε hsmall hbudget * ρ

/-- Purely scalar and source-geometric data sufficient for the CMP102
background-correction fixed point. -/
structure CMP102PhysicalBackgroundCorrectionScalarData
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : PhysicalGaugeOneCochain d (L * N') Nc)
    (ρ radius r s : ℝ) where
  rho_nonneg : 0 ≤ ρ
  dimension_two_le : 2 ≤ d
  blockScale_two_le : 2 ≤ L
  background_radius :
    cmp99SourceUbarFineDeviationRadius d L ε ≤ 1 / 3
  one_lt_radius : 1 < radius
  r_nonneg : 0 ≤ r
  r_lt_one : r < 1
  s_nonneg : 0 ≤ s
  s_lt_one : s < 1
  r_noWinding : (Nc : ℝ) * (r / (1 - r)) < 2 * Real.pi
  s_noWinding : (Nc : ℝ) * (s / (1 - s)) < 2 * Real.pi
  line_small :
    ∀ t, |t| < radius →
      |t| * cmp102PhysicalBackgroundBallSourceEnvelope
        U ha hP hε hsmall hbudget A ρ ≤ 1 / 2
  local_envelope :
    ∀ t, |t| < radius →
      1 / 3 + cmp102PhysicalContourDisplacementEnvelope d L
        (cmp102PhysicalBackgroundBallSourceEnvelope
          U ha hP hε hsmall hbudget A ρ) t ≤ r
  relative_envelope :
    ∀ t, |t| < radius →
      cmp102PhysicalBlockDisplacementEnvelope d L
        (cmp102PhysicalBackgroundBallSourceEnvelope
          U ha hP hε hsmall hbudget A ρ) t r ≤ s
  block_envelope_lt_one :
    cmp102PhysicalBlockDisplacementEnvelope d L
      (cmp102PhysicalBackgroundBallSourceEnvelope
        U ha hP hε hsmall hbudget A ρ) 1 r < 1
  correction_envelope_self :
    (Nc : ℝ) * cmp102PhysicalCorrectionSourceEnvelope d L
      (cmp102PhysicalBackgroundBallSourceEnvelope
        U ha hP hε hsmall hbudget A ρ) r ≤ ρ

namespace CMP102PhysicalBackgroundCorrectionScalarData

variable
    {U : PhysicalGaugeBackground d (L * N') Nc}
    {a CP ε : ℝ} {ha : 0 < a}
    {hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP}
    {hε : 0 ≤ ε} {hsmall : PhysicalWilsonSmallBackground U ε}
    {hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP}
    {A : PhysicalGaugeOneCochain d (L * N') Nc}
    {ρ radius r s : ℝ}
    (S : CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A ρ radius r s)

/-- Scalar source data construct the complete Banach-ball certificate. -/
noncomputable def toBallData :
    CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s where
  rho_nonneg := S.rho_nonneg
  r_nonneg := S.r_nonneg
  s_nonneg := S.s_nonneg
  chartBudget := by
    intro D hD
    let X :=
      A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
        (physicalGaugeOneCochainSupEquiv.symm D)
    have hX :
        cmp98SourceFieldSupNorm X ≤
          cmp102PhysicalBackgroundBallSourceEnvelope
            U ha hP hε hsmall hbudget A ρ := by
      simpa [X, cmp102PhysicalBackgroundBallSourceEnvelope] using
        cmp98SourceFieldSupNorm_physicalBackgroundShift_le
          U ha hP hε hsmall hbudget A D ρ hD
    exact cmp102PhysicalNonlinearChartBudget_of_envelope
      U X
      (cmp102PhysicalBackgroundBallSourceEnvelope
        U ha hP hε hsmall hbudget A ρ)
      radius r s hX S.one_lt_radius S.r_nonneg S.r_lt_one S.s_lt_one
      S.r_noWinding S.s_noWinding
      (cmp102PhysicalBackgroundBase_of_small
        S.dimension_two_le S.blockScale_two_le U ε hε hsmall
          S.background_radius)
      S.line_small S.local_envelope S.relative_envelope
  localRadius_eq := by
    intro D hD
    rfl
  relativeRadius_eq := by
    intro D hD
    rfl
  correction_self := by
    intro D hD
    let X :=
      A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
        (physicalGaugeOneCochainSupEquiv.symm D)
    have hX :
        cmp98SourceFieldSupNorm X ≤
          cmp102PhysicalBackgroundBallSourceEnvelope
            U ha hP hε hsmall hbudget A ρ := by
      simpa [X, cmp102PhysicalBackgroundBallSourceEnvelope] using
        cmp98SourceFieldSupNorm_physicalBackgroundShift_le
          U ha hP hε hsmall hbudget A D ρ hD
    have hsource :=
      cmp102PhysicalCorrectionSourceBudget_le_envelope X
        (cmp102PhysicalBackgroundBallSourceEnvelope
          U ha hP hε hsmall hbudget A ρ)
        r S.r_nonneg hX S.block_envelope_lt_one
    exact
      (mul_le_mul_of_nonneg_left hsource (Nat.cast_nonneg Nc)).trans
        S.correction_envelope_self

/-- **Scalar-source existence and uniqueness theorem.**  No chart family,
self-map estimate, or Lipschitz hypothesis appears in the interface. -/
theorem existsUnique_backgroundCorrection
    (hcontract :
      (S.toBallData).contractionRate < 1) :
    ∃! D : PhysicalGaugeOneCochainSup d N' Nc,
      ‖D‖ ≤ ρ ∧
        cmp102PhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget A ρ r s S.toBallData D = D :=
  S.toBallData.existsUnique_backgroundCorrection hcontract

/-- The scalar-source endpoint also exposes a solution of the literal
physical equation `D = C(A - H D)`. -/
theorem exists_backgroundCorrection_physicalEquation
    (hcontract :
      (S.toBallData).contractionRate < 1) :
    ∃ (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ),
      physicalGaugeOneCochainSupEquiv
          (cmp102PhysicalNonlinearCorrectionOfBudget U
            (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
              (physicalGaugeOneCochainSupEquiv.symm D))
            (S.toBallData.chartBudget D hD)) = D :=
  S.toBallData.exists_backgroundCorrection_physicalEquation hcontract

end CMP102PhysicalBackgroundCorrectionScalarData

end

end YangMills.RG
