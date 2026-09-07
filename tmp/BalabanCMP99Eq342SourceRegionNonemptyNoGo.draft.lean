import YangMills.RG.BalabanCMP99Eq335SourceRegionDictionary

/-!
SCRATCH ONLY: this file is neither imported nor compiler-verified and is not
evidence.

# Corollary-3.6 does not force a nonempty source carrier

The printed inclusion points from the source domain into the regular cube.
Consequently the empty source domain satisfies the dictionary for every
regular cube, although its active-site type has no inhabitant.  This is the
exact negative needed before indexing a family of Eq. (3.42) certificates,
whose finite supremum norm requires a nonempty carrier.
-/

namespace YangMills.RG

noncomputable section

/-- The literal empty active region. -/
def cmp99Eq342EmptySourceRegion (d N : ℕ) : ActiveGaugeRegion d N where
  sites := ∅

@[simp] theorem cmp99Eq342EmptySourceRegion_sites
    (d N : ℕ) :
    (cmp99Eq342EmptySourceRegion d N).sites = ∅ :=
  rfl

/-- The empty source region has no active-site inhabitant. -/
theorem not_nonempty_cmp99Eq342EmptySourceRegion_site
    {d N : ℕ} [NeZero N] :
    ¬ Nonempty (ActiveGaugeRegion.Site
      (cmp99Eq342EmptySourceRegion d N)) := by
  rintro ⟨x⟩
  simpa [cmp99Eq342EmptySourceRegion] using x.2

variable {L N' Mlarge n : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Mlarge]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}

/-- Every regular cube admits the empty Corollary-3.6 source dictionary. -/
theorem cmp99Eq342EmptySourceRegion_corollary36Dictionary
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos) :
    CMP99Eq335Corollary36SourceRegionDictionary
      (cmp99Eq342EmptySourceRegion 4 (L * N'))
      (cmp99Eq342EmptySourceRegion 4 (L * N')) C := by
  refine {
    headRegion_eq_omegaPrime0 := rfl
    printed_omegaPrime0_subset_regularCube := ?_
  }
  intro x hx
  simp [cmp99Eq342EmptySourceRegion] at hx

/-- The Corollary-3.6 dictionary therefore cannot produce the nonempty
carrier required by `CMP99Eq342SourceLocalizedGreenCertificate`. -/
theorem cmp99Eq342Corollary36Dictionary_does_not_force_nonempty
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos) :
    (CMP99Eq335Corollary36SourceRegionDictionary
        (cmp99Eq342EmptySourceRegion 4 (L * N'))
        (cmp99Eq342EmptySourceRegion 4 (L * N')) C) ∧
      ¬ Nonempty (ActiveGaugeRegion.Site
        (cmp99Eq342EmptySourceRegion 4 (L * N'))) := by
  exact ⟨cmp99Eq342EmptySourceRegion_corollary36Dictionary C,
    not_nonempty_cmp99Eq342EmptySourceRegion_site⟩

end

end YangMills.RG
