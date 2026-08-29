import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepth
import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientMetric
import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionPrecisionDecay
import YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay

/-!
SCRATCH ONLY: this file is neither imported nor compiler-verified and is not
evidence.  It is the depth-zero companion of the positive-depth D2 draft.

The theorem uses the literal zero-depth full-companion coefficient and the
internally constructed zero-depth Green.  No positive-depth Poincare premise
is introduced and no unrestricted Eq. (3.42) claim is made here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]
variable (OmegaSource : ActiveGaugeRegion 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)))
variable (regions : CMP99SourceActiveRegionChain 4 L
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) OmegaSource 0)
variable (hL : 2 ≤ L)
variable {spacing epsilon : ℝ}
variable (background : GaugeConfig 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) (SUN Nc))
variable (chain : CMP99SourceUbarRadiusChain 4 L Nc 0 epsilon)
variable (fineSmall : ∀ e : ConcreteEdge 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)),
  ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)

/-- Exact depth-zero precision amplitude.  The radius is `L^0`; it is left
visible rather than silently simplified so this statement is visibly the
base case of the D1 family. -/
noncomputable def
    cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
    (rate : ℝ) : ℝ :=
  cmp99SourceActiveRegionFullCompanionPrecisionUpperBound regions
      (by norm_num : 2 ≤ 4) hL (matrixSUNAdjointModel Nc) spacing epsilon
      background chain fineSmall *
    Real.exp (rate * (L ^ 0 : ℕ))

/-- The exact zero-depth ambient precision inherits D1 localization through
the named full-carrier metric equivalence. -/
theorem
    cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero_exponentialKernelBound
    (hspacing : 0 < spacing) {rate : ℝ} (hrate : 0 < rate) :
    FinitePiLpExponentialKernelBound
      (cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
        (Nc := Nc) (spacing := spacing)
        regions hL background chain fineSmall)
      (finBoxDist : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) →
        FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) → ℕ)
      (cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
        (Nc := Nc) (spacing := spacing)
        regions hL background chain fineSmall rate)
      rate := by
  let N := cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)
  let e := cmp99SourceFullActiveRegionSiteEquiv 4 N
  let Kactive := cmp99SourceActiveRegionFullCompanionPrecision regions
    (by norm_num : 2 ≤ 4) hL (matrixSUNAdjointModel Nc) spacing epsilon
    background chain fineSmall
  have hactive :=
    cmp99SourceActiveRegionFullCompanionPrecision_exponentialKernelBound
      regions (by norm_num : 2 ≤ 4) hL (matrixSUNAdjointModel Nc)
      hspacing hrate background chain fineSmall
  have hreindexed := finitePiLpTypedExponentialKernelBound_reindex
    e e Kactive (fun target source => finBoxDist target.1 source.1) hactive
  have hdist :
      (fun target source : FinBox 4 N =>
        finBoxDist (e.symm target).1 (e.symm source).1) =
      (finBoxDist : FinBox 4 N → FinBox 4 N → ℕ) := by
    funext target source
    have hmetric := finBoxDist_cmp99SourceFullActiveRegionSiteEquiv 4 N
      (e.symm target) (e.symm source)
    simpa [e] using hmetric.symm
  rw [hdist] at hreindexed
  simpa [N, Kactive,
    cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero,
    cmp99SourceActiveRegionFullCompanionAmbientPrecision,
    cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero] using
    hreindexed

/-- Exact zero-depth decay of the internally generated source Green. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_exponentialKernelBound
    (hspacing : 0 < spacing) {rate : ℝ} (hrate : 0 < rate) :
    let A :=
      cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
        (Nc := Nc) (spacing := spacing)
        regions hL background chain fineSmall rate
    let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
      (Nc := Nc) (spacing := spacing)
      regions hL background chain fineSmall
    FinitePiLpExponentialKernelBound
      (cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
        (Nc := Nc) regions hL hspacing background chain fineSmall)
      (fun target source : ActiveGaugeRegion.Site OmegaSource =>
        finBoxDist target.1 source.1)
      (2 / c)
      (finitePiLpExponentialInverseDecayRate A rate
        (cmp99OmegaSiteExpSumBound (rate / 4)) c) := by
  dsimp only
  let Ksource := cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
    (Nc := Nc) (spacing := spacing)
    regions hL background chain fineSmall
  let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
    (Nc := Nc) (spacing := spacing)
    regions hL background chain fineSmall
  have hc : 0 < c := by
    exact cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero
      regions (by norm_num : 2 ≤ 4) hL hspacing background chain fineSmall
  have hcoer : IsCoerciveCLM Ksource c := by
    exact isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
      (Nc := Nc) (spacing := spacing)
      regions hL background chain fineSmall
  have hK :=
    cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero_exponentialKernelBound
      (Nc := Nc) regions hL background chain fineSmall hspacing hrate
  have hG := cmp99RegionalDirichletGreen_exponentialKernelBound
    OmegaSource Ksource hc hcoer hK
  rw [cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_zero
    (Nc := Nc) regions hL hspacing background chain fineSmall] at hG
  simpa [Ksource, c] using hG

end

end YangMills.RG
