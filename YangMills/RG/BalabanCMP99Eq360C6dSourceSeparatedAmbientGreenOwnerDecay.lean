import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputAction
import YangMills.RG.BalabanCMP99SourceLocalizationOwnerDistanceBridge

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Exact C6d Green decay in source-owner distance

The fine-lattice rate is transported through the sealed inverse-scale bridge

`ell * ownerDist <= fineDist + 2 * (ell - 1)`.

Together with the one source-fibre payment already present in the exact input
action, this leaves the three boundary payments visible as
`exp (3 * rate * (ell - 1))`.  No uniform-in-depth conclusion is claimed.
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

/-- The exact positive-depth C6d Green on one source-owner input has the
block-rescaled rate `ell * rate`, with all three boundary payments visible.
This is per-depth and is not the uniform Eq. (3.42) certificate. -/
theorem norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_apply_le_ownerScale
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
    ‖cmp99Eq360C6dSourceSeparatedAmbientGreen
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall f target‖ ≤
      (ownerAmplitude * (ell : ℝ) ^ 2) *
        Real.exp (-(ownerRate *
          (finBoxDist owner
            (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) : ℝ))) *
        finitePiLpSupNorm f := by
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
  let ownerDist : ℝ :=
    (finBoxDist owner
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) : ℝ)
  let fineDist : ℝ := (finBoxDist root.1 target.1 : ℝ)
  let boundary : ℝ := ((ell - 1 : ℕ) : ℝ)
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
  have hbridgeNat :
      ell * finBoxDist owner
          (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) ≤
        finBoxDist root.1 target.1 + 2 * (ell - 1) := by
    rw [← hroot]
    simpa [ell, cmp99Eq342SourceLocalizedActiveOwner] using
      (cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary
        (L := L) (K := K) (Q := Q) depth root.1 target.1)
  have hbridgeCast :
      (ell : ℝ) *
          (finBoxDist owner
            (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) : ℝ) ≤
        (finBoxDist root.1 target.1 : ℝ) +
          2 * ((ell - 1 : ℕ) : ℝ) := by
    exact_mod_cast hbridgeNat
  have hbridge : (ell : ℝ) * ownerDist ≤ fineDist + 2 * boundary := by
    simpa [ownerDist, fineDist, boundary] using hbridgeCast
  have hexponent :
      -(rate * fineDist) ≤
        2 * rate * boundary - ownerRate * ownerDist := by
    dsimp [ownerRate]
    nlinarith [hrate.le, hbridge]
  have hexp :
      Real.exp (-(rate * fineDist)) ≤
        Real.exp (2 * rate * boundary - ownerRate * ownerDist) :=
    Real.exp_le_exp.mpr hexponent
  have htail : 0 ≤
      Real.exp (rate * boundary) * (ell : ℝ) ^ 2 * finitePiLpSupNorm f := by
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
      (finitePiLpSupNorm_nonneg f)
  have hbase :=
    norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_apply_le_sourceScale
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall hdecay owner root hroot f hf target
  calc
    ‖cmp99Eq360C6dSourceSeparatedAmbientGreen
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall f target‖ ≤
      (2 / c) * Real.exp (-(rate * fineDist)) *
        (Real.exp (rate * boundary) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
      simpa [ell, A, c, rate, fineDist, boundary] using hbase
    _ ≤ (2 / c) *
        Real.exp (2 * rate * boundary - ownerRate * ownerDist) *
        (Real.exp (rate * boundary) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp
          (div_nonneg (by positivity) hc.le)) htail
    _ = (ownerAmplitude * (ell : ℝ) ^ 2) *
        Real.exp (-(ownerRate * ownerDist)) * finitePiLpSupNorm f := by
      have hsplit :
          Real.exp (2 * rate * boundary - ownerRate * ownerDist) =
            Real.exp (2 * rate * boundary) *
              Real.exp (-(ownerRate * ownerDist)) := by
        rw [show 2 * rate * boundary - ownerRate * ownerDist =
          2 * rate * boundary + (-(ownerRate * ownerDist)) by ring,
          Real.exp_add]
      have hamp :
          Real.exp (2 * rate * boundary) * Real.exp (rate * boundary) =
            Real.exp (3 * rate * boundary) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      dsimp [ownerAmplitude]
      rw [show ((ell - 1 : ℕ) : ℝ) = boundary by rfl]
      rw [← hamp]
      ring

end

end YangMills.RG
