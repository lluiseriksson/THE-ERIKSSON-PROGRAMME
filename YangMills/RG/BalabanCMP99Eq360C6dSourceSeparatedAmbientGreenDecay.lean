import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen
import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientMetric
import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionPrecisionDecay
import YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Exact positive-depth C6d Green decay

The proof keeps all three transports explicit.  It first reindexes the
literal full-companion precision to the C6d ambient box, then pulls that same
operator to the source-separated carrier, and finally applies the canonical
regional inverse theorem.  No precision, Green, inverse equality, metric
equality or coercivity certificate is caller data.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

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

/-- The exact per-depth precision amplitude before the regional inverse.
The literal full-companion counting coefficient remains inside the named
upper bound; it is not replaced by a generated mass parameter. -/
noncomputable def cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude
    (rate : ℝ) : ℝ :=
  cmp99SourceActiveRegionFullCompanionPrecisionUpperBound regions
      (by norm_num : 2 ≤ 4) hL (matrixSUNAdjointModel Nc) eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
      (cmp99Eq360C6dSourceLaplacianRetainedExtension
        (R := R) (C := C) (hscale := hscale) regions)
      baselineRadiusBudget.toRadiusChain
      (norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le
        (R := R) (C := C) (hscale := hscale) (regions := regions)
        (D := D) (halpha1 := halpha1)
        (baselineRadiusBudget := baselineRadiusBudget)) *
    Real.exp (rate * (L ^ depth : ℕ))

/-- Reindex the exact full-companion precision to the literal C6d ambient
box, preserving periodic distance through the named full-carrier lemma. -/
theorem cmp99Eq360C6dSourceAmbientBaselinePrecision_exponentialKernelBound
    {rate : ℝ} (hrate : 0 < rate) :
    FinitePiLpExponentialKernelBound
      (cmp99Eq360C6dSourceAmbientBaselinePrecision
        (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
        (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
        (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1)
        (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
          (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
        (OmegaPrime0 := OmegaPrime0)
        R C hscale regions D hL halpha1 baselineRadiusBudget)
      (finBoxDist : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
        FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) → ℕ)
      (cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget rate)
      rate := by
  let e := cmp99SourceFullActiveRegionSiteEquiv 4
    (L ^ (depth + 1) * (2 * (K * Q)))
  let Kactive := cmp99SourceActiveRegionFullCompanionPrecision regions
    (by norm_num : 2 ≤ 4) hL (matrixSUNAdjointModel Nc) eta
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    (cmp99Eq360C6dSourceLaplacianRetainedExtension
      (R := R) (C := C) (hscale := hscale) regions)
    baselineRadiusBudget.toRadiusChain
    (norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le
      (R := R) (C := C) (hscale := hscale) (regions := regions)
      (D := D) (halpha1 := halpha1)
      (baselineRadiusBudget := baselineRadiusBudget))
  have hactive :=
    cmp99SourceActiveRegionFullCompanionPrecision_exponentialKernelBound
      regions (by norm_num : 2 ≤ 4) hL (matrixSUNAdjointModel Nc)
      R.eta_pos hrate
      (cmp99Eq360C6dSourceLaplacianRetainedExtension
        (R := R) (C := C) (hscale := hscale) regions)
      baselineRadiusBudget.toRadiusChain
      (norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le
        (R := R) (C := C) (hscale := hscale) (regions := regions)
        (D := D) (halpha1 := halpha1)
        (baselineRadiusBudget := baselineRadiusBudget))
  have hreindexed := finitePiLpTypedExponentialKernelBound_reindex
    e e Kactive (fun target source => finBoxDist target.1 source.1) hactive
  have hdist :
      (fun target source : FinBox 4
          (L ^ (depth + 1) * (2 * (K * Q))) =>
        finBoxDist (e.symm target).1 (e.symm source).1) =
      (finBoxDist : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
        FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) → ℕ) := by
    funext target source
    have hmetric := finBoxDist_cmp99SourceFullActiveRegionSiteEquiv 4
      (L ^ (depth + 1) * (2 * (K * Q))) (e.symm target) (e.symm source)
    simpa [e] using hmetric.symm
  rw [hdist] at hreindexed
  simpa [Kactive, cmp99Eq360C6dSourceAmbientBaselinePrecision,
    cmp99SourceActiveRegionFullCompanionAmbientPrecision,
    cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude] using
    hreindexed

/-- Pull the same ambient precision estimate to the source-separated C6d
carrier.  The metric conversion is a named theorem, not an implicit cast. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientPrecision_exponentialKernelBound
    {rate : ℝ} (hrate : 0 < rate) :
    FinitePiLpExponentialKernelBound
      (cmp99Eq360C6dSourceSeparatedAmbientPrecision
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget)
      (finBoxDist : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℕ)
      (cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget rate)
      rate := by
  let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  let Kambient := cmp99Eq360C6dSourceSeparatedC6dAmbientPrecision
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
  have hambient :=
    cmp99Eq360C6dSourceAmbientBaselinePrecision_exponentialKernelBound
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget hrate
  have hreindexed := finitePiLpTypedExponentialKernelBound_reindex
    e.symm e.symm Kambient
    (finBoxDist : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
      FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) → ℕ) hambient
  have hdist :
      (fun target source : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) =>
        finBoxDist (e.symm.symm target) (e.symm.symm source)) =
      (finBoxDist : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℕ) := by
    funext target source
    simpa [e] using
      (finBoxDist_cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
        L K Q depth target source)
  rw [hdist] at hreindexed
  simpa [Kambient, cmp99Eq360C6dSourceSeparatedC6dAmbientPrecision,
    cmp99Eq360C6dSourceSeparatedAmbientPrecision] using hreindexed

/-- Exact positive-depth decay of the canonical C6d source Green.  The
conclusion is per-depth; it is not yet the scale-uniform Eq. (3.42)
certificate. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientGreen_exponentialKernelBound
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1)
    {rate : ℝ} (hrate : 0 < rate) :
    let A := cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget rate
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
    FinitePiLpExponentialKernelBound
      (cmp99Eq360C6dSourceSeparatedAmbientGreen
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall)
      (fun target source : ActiveGaugeRegion.Site OmegaSource =>
        finBoxDist target.1 source.1)
      (2 / c)
      (finitePiLpExponentialInverseDecayRate A rate
        (cmp99OmegaSiteExpSumBound (rate / 4)) c) := by
  dsimp only
  let Ksource := cmp99Eq360C6dSourceSeparatedAmbientPrecision
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
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
  have hcoer : IsCoerciveCLM Ksource c := by
    exact isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall
  have hK :=
    cmp99Eq360C6dSourceSeparatedAmbientPrecision_exponentialKernelBound
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget hrate
  have hG := cmp99RegionalDirichletGreen_exponentialKernelBound
    OmegaSource Ksource hc hcoer hK
  rw [cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_ambient
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
    hdepth hsmall] at hG
  simpa [Ksource, c] using hG

end

end YangMills.RG
