import YangMills.RG.BalabanCMP99Eq335PhysicalRetainedNearIdentity

/-!


# CMP99 Corollary 3.6: source-fixed retained input package

This is the finite f5 prefix available before the four-action C6c.7 producer.
It applies the local near-identity theorem to the private retained recursion
and therefore constructs both retained prefixes and their terminal `Qprime`
equality.  It does not accept a small-field family, an exterior extension, a
tower or an operator equality.

No action estimate from CMP96 Proposition 2.2 is claimed here.  Those bounds
remain the named C6c.7 boundary.
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
variable {Omega : ActiveGaugeRegion 4 (L * N')}

/-- Construct the retained localized/canonical prefix package directly from
the source regularity witness.  The proof of local smallness is filled by f4;
it is not a parameter of this definition. -/
noncomputable def CMP99Eq335PhysicalRegularityWitness.localizedRetainedTower
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 spacing : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1)
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (hinside : CMP99Eq335RetainedFineReadCarrierInsideRegularCube
      (Nc := Nc) regions W.cube)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)) :
    CMP99SourceLocalizedRetainedTower regions (by norm_num : 2 ≤ 4) hM rho
      spacing (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
      W.transformedBackground chain
      (W.retainedFineReadBonds_nearIdentity regions hinside halpha1) :=
  cmp99SourceLocalizedRetainedTower regions (by norm_num) hM rho spacing
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    W.transformedBackground chain
    (W.retainedFineReadBonds_nearIdentity regions hinside halpha1)

/-- Terminal projection of the prefix equality generated internally above.
This is the locality bridge needed before gauge covariance and the C6c.7
action package can be composed. -/
theorem CMP99Eq335PhysicalRegularityWitness.localizedRetainedTerminalQprime_eq
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 spacing : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1)
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (hinside : CMP99Eq335RetainedFineReadCarrierInsideRegularCube
      (Nc := Nc) regions W.cube)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)) :
    let T := W.localizedRetainedTower (spacing := spacing)
      regions hM rho hinside halpha1 chain
    HEq (T.localizedTowerAt (Fin.last depth)).Qprime
      (T.canonicalTowerAt (Fin.last depth)).Qprime := by
  exact CMP99SourceLocalizedRetainedTower.terminalQprime_eq
    (W.localizedRetainedTower (spacing := spacing)
      regions hM rho hinside halpha1 chain)

end

end YangMills.RG
