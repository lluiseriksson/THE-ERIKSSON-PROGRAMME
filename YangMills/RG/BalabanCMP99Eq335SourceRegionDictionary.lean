import YangMills.RG.BalabanCMP99SourceRetainedCarrierEndpointGeometry
import YangMills.RG.BalabanCMP99Eq335PhysicalRetainedNearIdentity

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# CMP99 Corollary 3.6: source-domain dictionary for the regular cube

The primary p. 408 hypothesis is `Omega'_0 subset square`.  It does not mention
the recursively generated Lean read carrier.  This module keeps the printed
source region as an explicit type parameter, records separately the dictionary
identifying it with the head active region, and only then composes the printed
inclusion with the internally generated retained-carrier endpoint theorem.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L N' M Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero N'] [NeZero M] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}

/-- Source-facing dictionary for the geometric premise of Corollary 3.6.

`OmegaPrime0` is a parameter, not a hidden field.  The first law is the open
dictionary identifying the generated head region with the printed source
domain.  The second law is exactly the printed `Omega'_0 subset square`
premise.  No retained-carrier inclusion is stored. -/
structure CMP99Eq335Corollary36SourceRegionDictionary
    (Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N'))
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos) : Prop where
  headRegion_eq_omegaPrime0 : Omega = OmegaPrime0
  printed_omegaPrime0_subset_regularCube : OmegaPrime0.sites ⊆ C.carrier

/-- The recursive two-endpoint theorem plus the literal p. 408 dictionary
discharges the intermediate f4 carrier/cube gate.  The conclusion is generated
inside the proof; it is not a field of the source dictionary. -/
theorem CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth) :
    CMP99Eq335RetainedFineReadCarrierInsideRegularCube
      (Nc := Nc) regions C := by
  intro q hq
  have hendpoints :=
    regions.retainedFineReadBonds_endpointsIn (Nc := Nc) q hq
  have hsource : q.1 ∈ OmegaPrime0.sites := by
    rw [← D.headRegion_eq_omegaPrime0]
    exact hendpoints.1
  have htarget : q.1.shift q.2 ∈ OmegaPrime0.sites := by
    rw [← D.headRegion_eq_omegaPrime0]
    exact hendpoints.2
  exact ⟨D.printed_omegaPrime0_subset_regularCube hsource,
    D.printed_omegaPrime0_subset_regularCube htarget⟩

end

end YangMills.RG
