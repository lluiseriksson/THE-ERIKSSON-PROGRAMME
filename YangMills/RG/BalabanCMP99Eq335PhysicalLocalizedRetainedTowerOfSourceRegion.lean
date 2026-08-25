import YangMills.RG.BalabanCMP99Eq335SourceRegionDictionary
import YangMills.RG.BalabanCMP99Eq335PhysicalLocalizedRetainedTower

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# CMP99 Corollary 3.6: source-region closure of the retained prefix

This finite geometric wrapper removes the intermediate retained-carrier/cube
premise from f5a.  It derives that premise from the exact recursive endpoint
theorem and the printed source dictionary `Omega'_0 subset square`, then
constructs the retained localized/canonical prefix package internally.

It does not construct or accept any Green action estimate.  The C6c.7
four-action producer and the later gauge/operator transport remain absent.
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

/-- Construct the retained prefix directly from the printed source-region
dictionary.  The recursive read-carrier inclusion is a theorem consequence,
not a caller premise. -/
noncomputable def
    CMP99Eq335PhysicalRegularityWitness.localizedRetainedTowerOfSourceRegion
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 spacing : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary
      Omega OmegaPrime0 W.cube)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)) :
    CMP99SourceLocalizedRetainedTower regions (by norm_num : 2 ≤ 4) hM rho
      spacing (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
      W.transformedBackground chain
      (W.retainedFineReadBonds_nearIdentity regions
        (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
          W.cube D regions)
        halpha1) :=
  W.localizedRetainedTower (spacing := spacing) regions hM rho
    (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
      W.cube D regions)
    halpha1 chain

/-- The terminal retained `Qprime` equality after the source-region
dictionary has discharged the geometric gate internally. -/
theorem
    CMP99Eq335PhysicalRegularityWitness.localizedRetainedTerminalQprime_eq_ofSourceRegion
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 spacing : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary
      Omega OmegaPrime0 W.cube)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)) :
    let T := W.localizedRetainedTowerOfSourceRegion (spacing := spacing)
      regions D hM rho halpha1 chain
    HEq (T.localizedTowerAt (Fin.last depth)).Qprime
      (T.canonicalTowerAt (Fin.last depth)).Qprime := by
  exact CMP99SourceLocalizedRetainedTower.terminalQprime_eq
    (W.localizedRetainedTowerOfSourceRegion (spacing := spacing)
      regions D hM rho halpha1 chain)

end

end YangMills.RG
