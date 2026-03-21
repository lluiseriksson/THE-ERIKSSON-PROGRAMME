import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIPackageBridge

namespace YangMills.ClayCore

/-- Canonical public registry recording that the current live-target names for the
Balaban-RG / Haar-LSI lane all encode the same remaining obstruction. -/
structure BalabanRGUniformLSIEquivalenceRegistry (d N_c : ℕ) [NeZero N_c] : Prop where
  balabanToHaar :
    BalabanRGUniformLSILiveTarget d N_c ↔ HaarLSILiveTarget d N_c
  balabanToDirect :
    BalabanRGUniformLSILiveTarget d N_c ↔ SpecialUnitaryDirectUniformLSITheoremTarget d N_c
  balabanToConditional :
    BalabanRGUniformLSILiveTarget d N_c ↔ BalabanRGUniformLSIConditionalTarget d N_c
  balabanToPkgWitness :
    BalabanRGUniformLSILiveTarget d N_c ↔ ∃ pkg : BalabanRGPackage d N_c, True

/-- The current public live-target names admit a single canonical equivalence registry. -/
theorem balaban_rg_uniform_lsi_equivalence_registry
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGUniformLSIEquivalenceRegistry d N_c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact balaban_rg_uniform_lsi_live_target_iff_haar_lsi_live_target d N_c
  · exact balaban_rg_uniform_lsi_live_target_iff_direct_uniform_theorem_target d N_c
  · constructor
    · intro h
      exact (balaban_rg_uniform_lsi_live_target_iff_haar_lsi_live_target d N_c).1 h
    · intro h
      exact (balaban_rg_uniform_lsi_live_target_iff_haar_lsi_live_target d N_c).2 h
  · constructor
    · intro h
      exact (balaban_rg_uniform_lsi_live_target_iff_direct_uniform_theorem_target d N_c).1 h
    · intro h
      rcases h with ⟨pkg, _⟩
      exact balaban_rg_uniform_lsi_live_target_of_pkg pkg

/-- Old conditional name -> new structured public closure package. -/
theorem balaban_rg_uniform_lsi_closure_package_of_conditional_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : BalabanRGUniformLSIConditionalTarget d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  rcases h with ⟨pkg, _⟩
  exact balaban_rg_uniform_lsi_closure_package_of_pkg d N_c tr pkg

/-- Haar-lane live target -> new structured public closure package. -/
theorem balaban_rg_uniform_lsi_closure_package_of_haar_lsi_live_target
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : HaarLSILiveTarget d N_c) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  exact balaban_rg_uniform_lsi_closure_package_of_conditional_target d N_c tr h

/-- Bare package witness -> new structured public closure package. -/
theorem balaban_rg_uniform_lsi_closure_package_of_pkg_witness
    (d N_c : ℕ) [NeZero N_c]
    (tr : HaarLSIFromUniformLSITransfer N_c)
    (h : ∃ pkg : BalabanRGPackage d N_c, True) :
    BalabanRGUniformLSIClosurePackage d N_c := by
  rcases h with ⟨pkg, _⟩
  exact balaban_rg_uniform_lsi_closure_package_of_pkg d N_c tr pkg

/-- Old conditional name -> preferred public Balaban live-target name. -/
theorem balaban_rg_uniform_lsi_live_target_of_conditional_target
    {d N_c : ℕ} [NeZero N_c]
    (h : BalabanRGUniformLSIConditionalTarget d N_c) :
    BalabanRGUniformLSILiveTarget d N_c := by
  exact (balaban_rg_uniform_lsi_equivalence_registry d N_c).balabanToConditional.2 h

/-- Bare package witness -> preferred public Balaban live-target name. -/
theorem balaban_rg_uniform_lsi_live_target_of_pkg_witness
    {d N_c : ℕ} [NeZero N_c]
    (h : ∃ pkg : BalabanRGPackage d N_c, True) :
    BalabanRGUniformLSILiveTarget d N_c := by
  rcases h with ⟨pkg, _⟩
  exact balaban_rg_uniform_lsi_live_target_of_pkg pkg

end YangMills.ClayCore
