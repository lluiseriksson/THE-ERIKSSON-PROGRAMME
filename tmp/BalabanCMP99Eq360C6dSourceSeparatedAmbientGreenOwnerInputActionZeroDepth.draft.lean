import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayZeroDepth
import YangMills.RG.BalabanCMP99Eq342SourceOwnerTiltedInput
import YangMills.RG.FinitePiLpTiltedInverseAction

/-!
SCRATCH ONLY: this file is neither imported nor compiler-verified and is not
evidence.  It depends on the unsealed depth-zero D2 Green-decay draft.

# Exact depth-zero C6d Green action on one source-owner input

The depth-zero precision, Green, inverse identity and coercivity are all
constructed internally.  This is not obtained by specializing a theorem
whose hypotheses contain `0 < depth`.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

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

/-- The exact depth-zero Green acts on one source-owner input with the
printed `L^2` value scale. -/
theorem norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_apply_le_sourceScale
    (hspacing : 0 < spacing)
    {decay : ℝ} (hdecay : 0 < decay)
    (owner : FinBox 4 (2 * (K * Q)))
    (root : ActiveGaugeRegion.Site OmegaSource)
    (hroot : cmp99Eq342SourceLocalizedActiveOwner L K Q 0 root = owner)
    (f : FinitePiLpField (ActiveGaugeRegion.Site OmegaSource)
      (SUNLieCoord Nc))
    (hf : FinitePiLpSupportedInOwner
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0) owner f)
    (target : ActiveGaugeRegion.Site OmegaSource) :
    let ell := L ^ (0 + 1)
    let A :=
      cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
        (Nc := Nc) regions hL background chain fineSmall decay
    let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
      (Nc := Nc) regions hL background chain fineSmall
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    ‖cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
        (Nc := Nc) regions hL hspacing background chain fineSmall f target‖ ≤
      (2 / c) * Real.exp (-(rate * (finBoxDist root.1 target.1 : ℝ))) *
        (Real.exp (rate * ((ell - 1 : ℕ) : ℝ)) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
  dsimp only
  let ell := L ^ (0 + 1)
  let Kambient := cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
    (Nc := Nc) regions hL background chain fineSmall
  let Kregional := cmp99SourceAmbientDirichletPrecision OmegaSource Kambient
  let G := cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
    (Nc := Nc) regions hL hspacing background chain fineSmall
  let A :=
    cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
      (Nc := Nc) regions hL background chain fineSmall decay
  let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
    (Nc := Nc) regions hL background chain fineSmall
  let rowSum := cmp99OmegaSiteExpSumBound (decay / 4)
  let rate := finitePiLpExponentialInverseDecayRate A decay rowSum c
  let dist := fun target source : ActiveGaugeRegion.Site OmegaSource =>
    finBoxDist target.1 source.1
  letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
  have hc : 0 < c := by
    exact cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero
      regions (by norm_num : 2 ≤ 4) hL hspacing background chain fineSmall
  have hambientCoer : IsCoerciveCLM Kambient c := by
    exact isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
      (Nc := Nc) regions hL background chain fineSmall
  have hregionalCoer : IsCoerciveCLM Kregional c := by
    exact isCoerciveCLM_cmp99SourceAmbientDirichletPrecision
      OmegaSource Kambient hambientCoer
  have hKambient : FinitePiLpExponentialKernelBound Kambient
      (finBoxDist : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) →
        FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) → ℕ)
      A decay := by
    exact
      cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero_exponentialKernelBound
        (Nc := Nc) regions hL background chain fineSmall hspacing hdecay
  have hKregional : FinitePiLpExponentialKernelBound Kregional dist A decay := by
    exact cmp99RegionalDirichletPrecision_exponentialKernelBound
      OmegaSource Kambient hKambient
  have hrow : 0 ≤ rowSum := by
    unfold rowSum cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hexpSum : ∀ target,
      ∑ source, Real.exp (-((decay / 4) * (dist target source : ℝ))) ≤
        rowSum := by
    intro target
    exact activeGaugeRegion_finBoxDist_exp_sum_le OmegaSource target
      (div_pos hdecay (by norm_num))
  have hrate : 0 < rate := by
    exact finitePiLpExponentialInverseDecayRate_pos
      hKregional.1 hdecay hrow hc
  have hKC : Kregional.comp G = ContinuousLinearMap.id ℝ _ := by
    exact cmp99Eq360C6dSourceSeparatedDirichletPrecision_comp_green_zero
      (Nc := Nc) regions hL hspacing background chain fineSmall
  have htilt : IsCoerciveCLM
      (finitePiLpTiltConjCLM dist rate root Kregional) (c / 2) := by
    exact isCoerciveCLM_finitePiLpTiltConj_inverse_canonical
      dist
      (fun p q => finBoxDist_comm p.1 q.1)
      (fun p q r => finBoxDist_triangle p.1 q.1 r.1)
      Kregional hdecay hc hrow hKregional hregionalCoer hexpSum root
  have haction := norm_finitePiLpInverse_apply_le_of_tilted_coercive
    dist hc Kregional G hKC root htilt f target
  have hinput := norm_cmp99Eq342_sourceLocalizedTilt_le_sourceScale
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    0 OmegaSource owner root hroot hrate.le f hf
  calc
    ‖G f target‖ ≤
        (2 / c) * Real.exp (-(rate * (dist root target : ℝ))) *
          ‖finitePiLpTiltCLM (g := SUNLieCoord Nc) dist rate root f‖ :=
      haction
    _ ≤ (2 / c) * Real.exp (-(rate * (dist root target : ℝ))) *
        (Real.exp (rate * ((ell - 1 : ℕ) : ℝ)) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
      exact mul_le_mul_of_nonneg_left hinput
        (mul_nonneg (div_nonneg (by positivity) hc.le)
          (Real.exp_pos _).le)

end

end YangMills.RG
