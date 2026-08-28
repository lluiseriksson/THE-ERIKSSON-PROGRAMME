import YangMills.RG.BalabanCMP99ActiveRegionCanonicalAmbientCompletion
import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen

/-!
PRE-VALIDATION: scratch source only; no `.olean` has been materialized for
this file and no compiler or axiom-oracle verdict is claimed.

# Canonical ambient completion of the exact C6d source Green

This source-facing composition closes the carrier round trip without taking
an ambient completion or an equality of Greens from the caller.  It first
compresses the one C6d source ambient precision, completes that regional
operator by the canonical exterior identity, and then proves that the Green
generated from the completion is the already constructed C6d source Green.

The statement is only an inverse/carrier dictionary.  It does not produce
any of the four physical Eq. (3.42) action bounds or the constants `B0` and
`delta0`.
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

/-- Completing the literal regional compression of the one C6d source
ambient precision leaves its internally generated source Green unchanged.
No ambient operator, regional Green, or equality of inverses is caller data.
-/
theorem cmp99Eq360C6dSourceSeparatedCanonicalAmbientCompletion_green_eq
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    let A := cmp99Eq360C6dSourceSeparatedAmbientPrecision
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
    let hc : 0 < c := cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
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
    let hA : IsCoerciveCLM A c :=
      isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall
    cmp99RegionalDirichletGreen OmegaSource
        (cmp99ActiveRegionCanonicalAmbientCompletion OmegaSource
          (cmp99RegionalDirichletPrecision OmegaSource A))
        (lt_min hc zero_lt_one)
        (isCoerciveCLM_cmp99ActiveRegionCanonicalAmbientCompletion
          OmegaSource (cmp99RegionalDirichletPrecision OmegaSource A)
          (isCoerciveCLM_cmp99RegionalDirichletPrecision OmegaSource A hA)) =
      cmp99Eq360C6dSourceSeparatedAmbientGreen
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall := by
  dsimp only
  calc
    _ = cmp99RegionalDirichletGreen OmegaSource A hc hA :=
      cmp99RegionalDirichletGreen_canonicalAmbientCompletion_compressed_eq
        OmegaSource A hc hA
    _ = cmp99Eq360C6dSourceSeparatedAmbientGreen
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall :=
      cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_ambient
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall

end

end YangMills.RG
