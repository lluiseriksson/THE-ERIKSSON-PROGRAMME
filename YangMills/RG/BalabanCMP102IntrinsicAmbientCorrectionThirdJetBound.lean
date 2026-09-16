/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientNonlinearBlockThirdJetBound
import YangMills.RG.BalabanCMP102IntrinsicAmbientCorrectionSourceBudget
import YangMills.RG.BalabanCMP102AmbientLocalNearLogThirdJetBound
import YangMills.RG.BalabanCMP98AdBinomial

/-!
# Third jet of the intrinsic ambient CMP102 correction

The represented nonlinear block has a generated physical third-jet budget.
This file transports that budget through the fixed right normalizer and the
literal relative Mercator logarithm.  The linear subtraction in equation
(122) vanishes exactly in derivative order three.

No third derivative of the represented block, relative deviation, or
intrinsic correction is accepted from the caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
  [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102IntrinsicAmbientCorrectionThirdJetMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

local instance cmp102IntrinsicAmbientCorrectionThirdJetSourceCLMNorm :
    Norm
      (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp102IntrinsicAmbientCorrectionThirdJetSourceCLMSeminormed :
    SeminormedAddCommGroup
      (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp102IntrinsicAmbientCorrectionThirdJetSourceCLMNormedSpace :
    NormedSpace ℝ
      (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousLinearMap.toNormedSpace

local instance cmp102IntrinsicAmbientCorrectionThirdJetCMLSeminormed (n : ℕ) :
    SeminormedAddCommGroup
      (PhysicalAmbientMatrixTangent d (M * N') Nc [×n]→L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousMultilinearMap.seminormedAddCommGroup

/-- Common positive-jet budget of the represented block after multiplication
by its fixed background normalizer. -/
def cmp102SourceAmbientRelativeDeviationThirdJetBudget
    (d M : ℕ) (r q : NNReal) : ℝ :=
  cmp102SourceAmbientNonlinearBlockThirdJetBudget
      (Nc := Nc) d M r q *
    cmp98SourceOuterExpNormBudget q

/-- Inner radius used in the local Faà di Bruno estimate. -/
def cmp102SourceAmbientRelativeDeviationCompositionRadius
    (d M : ℕ) (r q : NNReal) : ℝ :=
  max 1
    (cmp102SourceAmbientRelativeDeviationThirdJetBudget
      (Nc := Nc) d M r q)

/-- Generated third-jet budget of the intrinsic ambient correction. -/
def cmp102SourceIntrinsicAmbientCorrectionThirdJetBudget
    (d M : ℕ) (r q s : NNReal) : ℝ :=
  6 * cmp102SourceNearLogOrderThreeOuterBudget
        (Nc := Nc) s *
    cmp102SourceAmbientRelativeDeviationCompositionRadius
        (Nc := Nc) d M r q ^ 3

theorem norm_cmp98RightMulCLM_le
    (I : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ContinuousLinearMap.opNorm (cmp98RightMulCLM I) ≤ ‖I‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg I)
  intro H
  simpa using norm_mul_le H I

set_option maxHeartbeats 1200000 in
/-- Every positive jet through order three of the normalized relative
deviation is generated from the represented-block jets and the source
normalizer bound. -/
theorem norm_iteratedFDeriv_cmp102AmbientRelativeDeviation_le_sourceThirdJetBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r q : NNReal) (hZ : ‖Z‖ < r)
    (hq13 : (1 / 3 : ℝ) ≤ q) (hq1 : (q : ℝ) < 1)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < q)
    (i : ℕ) (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    ‖iteratedFDeriv ℝ i
        (fun W =>
          cmp102AmbientNonlinearBlock U b W *
              cmp98Eq119NonlinearBlockInverseAtZero U
                (0 : PhysicalGaugeOneCochain d (M * N') Nc) b -
            1) Z‖ ≤
      cmp102SourceAmbientRelativeDeviationThirdJetBudget
        (Nc := Nc) d M r q := by
  let block :=
    cmp102AmbientNonlinearBlock U b
  let I :=
    cmp98Eq119NonlinearBlockInverseAtZero U
      (0 : PhysicalGaugeOneCochain d (M * N') Nc) b
  let right :
      Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    cmp98RightMulCLM I
  let normalized :
      PhysicalAmbientMatrixTangent d (M * N') Nc →
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    right ∘ block
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1 :=
    fun x hx => (hD x hx).trans hq1
  have hblock : ContDiffAt ℝ ⊤ block Z := by
    let E := cmp98UbarExpAverage U b
    let C :
        PhysicalAmbientMatrixTangent d (M * N') Nc →
          Matrix (Fin Nc) (Fin Nc) ℂ :=
      fun W => cmp98AmbientWilsonLineMatrix U W
        (cmp98SourceCoarseBondPath (Nc := Nc) b)
    have hE : AnalyticAt ℝ E Z :=
      analyticAt_cmp98UbarExpAverage_of_norm_lt_one U b Z hsmall
    have hC : AnalyticAt ℝ C Z :=
      analyticAt_cmp98AmbientWilsonLineMatrix U Z
        (cmp98SourceCoarseBondPath (Nc := Nc) b)
    simpa [block, cmp102AmbientNonlinearBlock, E, C] using
      (hE.mul hC).contDiffAt
  have hnormalized : ContDiffAt ℝ ⊤ normalized Z :=
    hblock.continuousLinearMap_comp right
  have hconst : ContDiffAt ℝ ⊤
      (fun _ : PhysicalAmbientMatrixTangent d (M * N') Nc =>
        (1 : Matrix (Fin Nc) (Fin Nc) ℂ)) Z :=
    contDiffAt_const
  have hfun :
      (fun W =>
        cmp102AmbientNonlinearBlock U b W * I - 1) =
        normalized - fun _ => (1 : Matrix (Fin Nc) (Fin Nc) ℂ) := by
    funext W
    change block W * I - 1 = right (block W) - 1
    simp [right, cmp98RightMulCLM_apply]
  have hjet :
      iteratedFDeriv ℝ i
          (fun W =>
            cmp102AmbientNonlinearBlock U b W * I - 1) Z =
        right.compContinuousMultilinearMap
          (iteratedFDeriv ℝ i block Z) := by
    rw [hfun,
      iteratedFDeriv_sub_apply
        (hnormalized.of_le
          le_top)
        (hconst.of_le
          le_top)]
    have hconstJet :
        iteratedFDeriv ℝ i
          (fun _ : PhysicalAmbientMatrixTangent d (M * N') Nc =>
            (1 : Matrix (Fin Nc) (Fin Nc) ℂ)) Z = 0 :=
      iteratedFDeriv_const_of_ne (by omega) _
    rw [hconstJet, sub_zero]
    exact right.iteratedFDeriv_comp_left hblock
      (WithTop.coe_le_coe.mpr
        (WithTop.coe_le_coe.mpr hi3))
  have hI :
      ‖I‖ ≤ cmp98SourceOuterExpNormBudget q := by
    simpa [I] using
      norm_cmp98Eq119NonlinearBlockInverseAtZero_le_sourceBudget
        U (0 : PhysicalGaugeOneCochain d (M * N') Nc) b q
          hbase hq13 hq1
  have hblockJet :
      ‖iteratedFDeriv ℝ i block Z‖ ≤
        cmp102SourceAmbientNonlinearBlockThirdJetBudget
          (Nc := Nc) d M r q := by
    simpa [block] using
      norm_iteratedFDeriv_cmp102AmbientNonlinearBlock_le_orderThreeBudget
        U b Z r q hZ hq1 hD i hi3
  rw [hjet]
  calc
    ‖right.compContinuousMultilinearMap
        (iteratedFDeriv ℝ i block Z)‖
        ≤ ContinuousLinearMap.opNorm right *
            ‖iteratedFDeriv ℝ i block Z‖ :=
      right.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖I‖ *
        cmp102SourceAmbientNonlinearBlockThirdJetBudget
          (Nc := Nc) d M r q := by
      exact mul_le_mul (norm_cmp98RightMulCLM_le I) hblockJet
        (norm_nonneg _) (norm_nonneg _)
    _ ≤ cmp98SourceOuterExpNormBudget q *
        cmp102SourceAmbientNonlinearBlockThirdJetBudget
          (Nc := Nc) d M r q := by
      have hbudget0 :
          0 ≤ cmp102SourceAmbientNonlinearBlockThirdJetBudget
            (Nc := Nc) d M r q :=
        (norm_nonneg (iteratedFDeriv ℝ i block Z)).trans hblockJet
      exact mul_le_mul_of_nonneg_right hI
        hbudget0
    _ = cmp102SourceAmbientRelativeDeviationThirdJetBudget
        (Nc := Nc) d M r q := by
      simp [cmp102SourceAmbientRelativeDeviationThirdJetBudget, mul_comm]

set_option maxHeartbeats 1800000 in
/-- The literal intrinsic ambient correction has a fully generated third
jet: represented block, fixed normalizer, relative Mercator logarithm, and
linear subtraction are all constructed internally. -/
theorem norm_iteratedFDeriv_three_cmp102IntrinsicAmbientCorrectionBond_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r q s : NNReal) (hZ : ‖Z‖ < r)
    (hq13 : (1 / 3 : ℝ) ≤ q) (hq1 : (q : ℝ) < 1)
    (hs1 : (s : ℝ) < 1)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < q)
    (hdev :
      cmp102SourceAmbientRelativeDeviationValueBudget
          d M r q < s) :
    ‖iteratedFDeriv ℝ 3
        (cmp102IntrinsicAmbientCorrectionBond U b) Z‖ ≤
      cmp102SourceIntrinsicAmbientCorrectionThirdJetBudget
        (Nc := Nc) d M r q s := by
  let block :=
    cmp102AmbientNonlinearBlock U b
  let I :=
    cmp98Eq119NonlinearBlockInverseAtZero U
      (0 : PhysicalGaugeOneCochain d (M * N') Nc) b
  let inner :
      PhysicalAmbientMatrixTangent d (M * N') Nc →
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun W => block W * I - 1
  let outer :
      Matrix (Fin Nc) (Fin Nc) ℂ →
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    nearLog
  let D :=
    cmp102SourceAmbientRelativeDeviationCompositionRadius
      (Nc := Nc) d M r q
  let C :=
    cmp102SourceNearLogOrderThreeOuterBudget
      (Nc := Nc) s
  have hq0 : (0 : ℝ) ≤ q :=
    (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hq13
  have hinnerValue :
      ‖inner Z‖ < s := by
    have hraw :=
      norm_cmp102AmbientRelativeDeviation_le_sourceBudget
        U b Z (r := (r : ℝ)) (q := (q : ℝ))
          r.2 hq13 hq1 hZ.le hbase (fun x hx => (hD x hx).le)
    exact hraw.trans_lt hdev
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1 :=
    fun x hx => (hD x hx).trans hq1
  have hblock : ContDiffAt ℝ ⊤ block Z := by
    let E := cmp98UbarExpAverage U b
    let Wline :
        PhysicalAmbientMatrixTangent d (M * N') Nc →
          Matrix (Fin Nc) (Fin Nc) ℂ :=
      fun W => cmp98AmbientWilsonLineMatrix U W
        (cmp98SourceCoarseBondPath (Nc := Nc) b)
    have hE : AnalyticAt ℝ E Z :=
      analyticAt_cmp98UbarExpAverage_of_norm_lt_one U b Z hsmall
    have hWline : AnalyticAt ℝ Wline Z :=
      analyticAt_cmp98AmbientWilsonLineMatrix U Z
        (cmp98SourceCoarseBondPath (Nc := Nc) b)
    simpa [block, cmp102AmbientNonlinearBlock, E, Wline] using
      (hE.mul hWline).contDiffAt
  have hinnerSmooth : ContDiffAt ℝ 3 inner Z := by
    have hmul : AnalyticAt ℝ (fun W => block W * I) Z :=
      hblock.analyticAt.mul analyticAt_const
    exact (hmul.sub analyticAt_const).contDiffAt
  have houterSmooth : ContDiffAt ℝ 3 outer (inner Z) :=
    (analyticAt_nearLog_of_norm_lt_one
      (hinnerValue.trans hs1)).contDiffAt
  have hC : ∀ i, i ≤ 3 →
      ‖iteratedFDeriv ℝ i outer (inner Z)‖ ≤ C := by
    intro i hi
    exact norm_iteratedFDeriv_nearLog_le_orderThreeOuterBudget
      s hs1 hinnerValue i hi
  have hDone : 1 ≤ D :=
    le_max_left _ _
  have hDnonneg : 0 ≤ D :=
    zero_le_one.trans hDone
  have hDjets : ∀ i, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i inner Z‖ ≤ D ^ i := by
    intro i hi1 hi3
    have hraw :
        ‖iteratedFDeriv ℝ i inner Z‖ ≤
          cmp102SourceAmbientRelativeDeviationThirdJetBudget
            (Nc := Nc) d M r q := by
      simpa [inner, block, I] using
        norm_iteratedFDeriv_cmp102AmbientRelativeDeviation_le_sourceThirdJetBudget
          U b Z r q hZ hq13 hq1 hbase hD i hi1 hi3
    calc
      ‖iteratedFDeriv ℝ i inner Z‖
          ≤ cmp102SourceAmbientRelativeDeviationThirdJetBudget
              (Nc := Nc) d M r q := hraw
      _ ≤ D := le_max_right _ _
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ i := pow_le_pow_right₀ hDone hi1
  have hcomp :=
    norm_iteratedFDeriv_comp_le_at_of_both_local
      houterSmooth hinnerSmooth hC hDjets
  have hlog :
      ‖iteratedFDeriv ℝ 3 (outer ∘ inner) Z‖ ≤
        6 * C * D ^ 3 := by
    simpa using hcomp
  let linear :
      PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    (cmp98RightMulCLM I).comp
      (fderiv ℝ block 0)
  have hlinearThird :
      iteratedFDeriv ℝ 3 linear Z = 0 := by
    rw [show 3 = 2 + 1 by omega, iteratedFDeriv_succ_eq_comp_right]
    have hderiv :
        (fun y =>
          fderiv ℝ linear y) =
          fun _ => linear := by
      funext y
      exact linear.fderiv
    rw [hderiv, iteratedFDeriv_const_of_ne (by omega : 2 ≠ 0)]
    simp
  have hfun :
      cmp102IntrinsicAmbientCorrectionBond U b =
        (outer ∘ inner) - linear := by
    funext W
    simp only [cmp102IntrinsicAmbientCorrectionBond, outer, inner,
      linear, block, I, Function.comp_apply, Pi.sub_apply]
    change
      nearLog
          (cmp102AmbientNonlinearBlock U b W *
              cmp98Eq119NonlinearBlockInverseAtZero U 0 b - 1) -
            fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 W *
              cmp98Eq119NonlinearBlockInverseAtZero U 0 b =
        nearLog
          (cmp102AmbientNonlinearBlock U b W *
              cmp98Eq119NonlinearBlockInverseAtZero U 0 b - 1) -
            cmp98RightMulCLM
              (cmp98Eq119NonlinearBlockInverseAtZero U 0 b)
              (fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 W)
    rw [cmp98RightMulCLM_apply]
  have hlogSmooth : ContDiffAt ℝ 3 (outer ∘ inner) Z :=
    houterSmooth.comp Z hinnerSmooth
  have hlinearSmooth : ContDiffAt ℝ 3 linear Z :=
    linear.contDiff.contDiffAt
  rw [hfun,
    iteratedFDeriv_sub_apply hlogSmooth hlinearSmooth,
    hlinearThird, sub_zero]
  exact hlog

end

end YangMills.RG
