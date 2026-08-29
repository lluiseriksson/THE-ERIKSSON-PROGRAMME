import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecay

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Exact C6d block-localized Green value bound

The source-facing predicate quantifies over every owner.  If an owner fibre is
empty, its support hypothesis forces the input to vanish.  Otherwise the
representing source site is constructed internally and the exact owner-decay
theorem is applied.  This remains per-depth.
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

/-- Per-depth value action for every source owner on the exact positive-depth
C6d Green.  The explicit `root` supplies only the carrier instance; it is not
required to lie in the owner currently quantified by the predicate. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientGreen_blockLocalizedSupBound
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1)
    {decay : ℝ} (hdecay : 0 < decay)
    (root : ActiveGaugeRegion.Site OmegaSource) :
    letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
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
    let ownerRate := (ell : ℝ) * rate
    let ownerAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    FinitePiLpTypedBlockLocalizedSupBound
      (cmp99Eq360C6dSourceSeparatedAmbientGreen
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (ownerAmplitude * (ell : ℝ) ^ 2) ownerRate := by
  dsimp only
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
  let ownerRate := (ell : ℝ) * rate
  let ownerAmplitude := (2 / c) *
    Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
  let G := cmp99Eq360C6dSourceSeparatedAmbientGreen
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
    hdepth hsmall
  letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
  have hA : 0 ≤ A := by
    exact (cmp99Eq360C6dSourceSeparatedAmbientPrecision_exponentialKernelBound
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdecay).1
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
  have hrow : 0 ≤ cmp99OmegaSiteExpSumBound (decay / 4) := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hrate : 0 < rate := by
    exact finitePiLpExponentialInverseDecayRate_pos hA hdecay hrow hc
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (depth + 1)
  have hownerAmplitude : 0 ≤ ownerAmplitude := by
    exact mul_nonneg (div_nonneg (by positivity) hc.le) (Real.exp_pos _).le
  refine ⟨mul_nonneg hownerAmplitude (sq_nonneg _),
    mul_pos hell hrate, ?_⟩
  intro owner f hf target
  by_cases howner : ∃ source : ActiveGaugeRegion.Site OmegaSource,
      cmp99Eq342SourceLocalizedActiveOwner L K Q depth source = owner
  · rcases howner with ⟨source, hsource⟩
    have hbase :=
      norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_apply_le_ownerScale
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall hdecay owner source hsource f hf target
    simpa [G, ell, A, c, rate, ownerRate, ownerAmplitude,
      finBoxDist_comm] using hbase
  · have hfzero : f = 0 := by
      apply PiLp.ext
      intro source
      apply hf source
      intro hsource
      exact howner ⟨source, hsource⟩
    subst f
    have hzero : G (0 : ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc))
        target = 0 := by
      simp only [map_zero, PiLp.zero_apply]
    rw [hzero, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hownerAmplitude (sq_nonneg _))
        (Real.exp_pos _).le)
      (finitePiLpSupNorm_nonneg 0)

end

end YangMills.RG
