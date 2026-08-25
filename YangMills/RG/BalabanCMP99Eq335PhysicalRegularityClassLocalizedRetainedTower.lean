import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClass
import YangMills.RG.BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# CMP99 (3.35) class membership to the selected Corollary-3.6 region

The regional prefix must not receive a freely chosen one-cube regularity
witness.  This wrapper specializes the source's all-admissible-cubes class
membership to the cube selected by the literal `Omega'_0 subset square`
dictionary, adds the separate Corollary-3.6 scalar gate, and constructs that
witness internally.

It proves no Green estimate and does not assert that an arbitrary background
belongs to the regularity class.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {L N' M Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero N'] [NeZero M] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}

/-- Construct the retained regional prefix from literal (3.35) class
membership.  The one-cube witness is a local definition, not an input. -/
noncomputable def
    CMP99Eq335PhysicalRegularityClass.localizedRetainedTowerOfSourceRegion
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 spacing : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)) :
    let W := R.toCubeWitness C alpha1 hscale
    CMP99SourceLocalizedRetainedTower regions (by norm_num : 2 ≤ 4) hM rho
      spacing (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
      W.transformedBackground chain
      (W.retainedFineReadBonds_nearIdentity regions
        (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
          C D regions)
        halpha1) := by
  let W := R.toCubeWitness C alpha1 hscale
  exact W.localizedRetainedTowerOfSourceRegion
    (spacing := spacing) regions D hM rho halpha1 chain

/-- The terminal retained `Qprime` identity with the per-region regularity
witness eliminated from the public contract. -/
theorem
    CMP99Eq335PhysicalRegularityClass.localizedRetainedTerminalQprime_eq_ofSourceRegion
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 spacing : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)) :
    let W := R.toCubeWitness C alpha1 hscale
    let T := R.localizedRetainedTowerOfSourceRegion
      (spacing := spacing) C hscale regions D hM rho halpha1 chain
    HEq (T.localizedTowerAt (Fin.last depth)).Qprime
      (T.canonicalTowerAt (Fin.last depth)).Qprime := by
  let W := R.toCubeWitness C alpha1 hscale
  exact W.localizedRetainedTerminalQprime_eq_ofSourceRegion
    (spacing := spacing) regions D hM rho halpha1 chain

end

end YangMills.RG
