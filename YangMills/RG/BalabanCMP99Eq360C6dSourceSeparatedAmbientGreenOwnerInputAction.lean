import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecay
import YangMills.RG.BalabanCMP99Eq342SourceOwnerTiltedInput
import YangMills.RG.FinitePiLpTiltedInverseAction

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Exact C6d Green action on one source-owner input

The proof does not expand the input into coordinate probes.  It reconstructs
the canonical rooted tilted coercivity for the literal C6d Dirichlet
precision, applies the arbitrary-input inverse lemma, and spends the sealed
`ell^2 * supNorm` source conversion exactly once.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {L K Q Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification
  (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}
variable {U : PhysicalGaugeBackground 4
  (L ^ (depth + 1) * (2 * (K * Q))) Nc}
variable {eta alpha0 alpha1 : ℝ}
variable (OmegaSource : ActiveGaugeRegion 4
  (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
variable (R : CMP99Eq335PhysicalRegularityClass
  (L := L ^ (depth + 1)) (N' := 2 * (K * Q))
  (Mlarge := Mlarge) (Nc := Nc) (n := n)
  (scaleExtent := scaleExtent) (S := S)
  (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
variable (C : CMP99SourceRegularCube
  (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) n Mlarge
  scaleExtent S scaleExtent_pos)
variable (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
variable {OmegaPrime0 : ActiveGaugeRegion 4
  (L ^ (depth + 1) * (2 * (K * Q)))}
variable (regions : CMP99SourceActiveRegionChain 4 L
  (L ^ (depth + 1) * (2 * (K * Q)))
  (cmp99Eq360C6dSourceSeparatedAmbientRegion
    (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource) depth)
variable (D : CMP99Eq335Corollary36SourceRegionDictionary
  (cmp99Eq360C6dSourceSeparatedAmbientRegion
    (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
  OmegaPrime0 C)
variable (hL : 2 ≤ L) (halpha1 : alpha1 ≤ 1 / 2)
variable (baselineRadiusBudget : CMP99SourceUbarClosedBudget 4 L Nc depth
  (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))

/-- The exact positive-depth C6d Green acts on one complete source-owner
input with the printed `ell^2` scale.  No precision, Green, inverse identity,
tilted coercivity or metric equality is caller data. -/
theorem norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_apply_le_sourceScale
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1)
    {decay : ℝ} (hdecay : 0 < decay)
    (owner : FinBox 4 (2 * (K * Q)))
    (root : ActiveGaugeRegion.Site OmegaSource)
    (hroot : cmp99Eq342SourceLocalizedActiveOwner L K Q depth root = owner)
    (f : FinitePiLpField (ActiveGaugeRegion.Site OmegaSource)
      (SUNLieCoord Nc))
    (hf : FinitePiLpSupportedInOwner
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth) owner f)
    (target : ActiveGaugeRegion.Site OmegaSource) :
    let ell := L ^ (depth + 1)
    let A := cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget decay
    let c := cmp99Eq360C6dSourceBaselinePhysicalCoercivity
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    ‖cmp99Eq360C6dSourceSeparatedAmbientGreen
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall f target‖ ≤
      (2 / c) * Real.exp (-(rate * (finBoxDist root.1 target.1 : ℝ))) *
        (Real.exp (rate * ((ell - 1 : ℕ) : ℝ)) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
  dsimp only
  let ell := L ^ (depth + 1)
  let Kambient := cmp99Eq360C6dSourceSeparatedAmbientPrecision
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
  let Kregional := cmp99SourceAmbientDirichletPrecision OmegaSource Kambient
  let G := cmp99Eq360C6dSourceSeparatedAmbientGreen
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
    hdepth hsmall
  let A := cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget decay
  let c := cmp99Eq360C6dSourceBaselinePhysicalCoercivity
    (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
    (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
    (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1)
    (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
      (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
    (OmegaPrime0 := OmegaPrime0)
    R C hscale regions D hL halpha1 baselineRadiusBudget
  let rowSum := cmp99OmegaSiteExpSumBound (decay / 4)
  let rate := finitePiLpExponentialInverseDecayRate A decay rowSum c
  let dist := fun target source : ActiveGaugeRegion.Site OmegaSource =>
    finBoxDist target.1 source.1
  letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
  have hc : 0 < c := by
    exact cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall
  have hambientCoer : IsCoerciveCLM Kambient c := by
    exact isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall
  have hregionalCoer : IsCoerciveCLM Kregional c := by
    exact isCoerciveCLM_cmp99SourceAmbientDirichletPrecision
      OmegaSource Kambient hambientCoer
  have hKambient : FinitePiLpExponentialKernelBound Kambient
      (finBoxDist : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℕ)
      A decay := by
    exact cmp99Eq360C6dSourceSeparatedAmbientPrecision_exponentialKernelBound
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget hdecay
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
    exact cmp99Eq360C6dSourceSeparatedAmbientPrecision_comp_green
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall
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
    depth OmegaSource owner root hroot hrate.le f hf
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
