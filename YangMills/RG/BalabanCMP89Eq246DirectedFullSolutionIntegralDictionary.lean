import YangMills.RG.BalabanCMP89Eq246DirectedNormalizedFullSolutionIntegral
import YangMills.RG.BalabanCMP89Eq246FinePointSourceHolomorphy

/-!
# PRE-VALIDATION: directed CMP89 (2.46) synthesis dictionary

Source is present, its promoted `.olean` has not yet been materialized in a
fresh checkout, and the result has not yet been cold-verified by the compiler.

The central-plus-noncentral directed sum is identified algebraically with the
already constructed complete fine-point-source integrand evaluated on its
endpoint-selected signed contour.  This is not a contour-deformation theorem:
it does not yet identify the signed-contour integral with the real-slice
physical Green, a finite periodic Green, or a generated regional Green.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The directed central-plus-noncentral decomposition is exactly the full
fine-to-fine point-source integrand on the selected signed contour. -/
theorem cmp89Eq246DirectedFullSolutionSum_eq_signedContourIntegrand
    (L j : ℕ) [NeZero L] (mass a rho : ℝ)
    (p targetEndpoint sourceEndpoint : Fin 4 → ℝ) :
    cmp89Eq246DirectedFullSolutionSum
        L j mass a rho p targetEndpoint sourceEndpoint =
      cmp89Eq246StabilizedFineToFineGreenIntegrand 4 L j mass a
        (cmp89Eq251SignedContourMomentum rho p
          (fun mu => targetEndpoint mu - sourceEndpoint mu))
        targetEndpoint sourceEndpoint := by
  classical
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let term : CMP89Eq246AliasIndex 4 L j → ℂ := fun m =>
    Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint) *
      cmp89Eq246StabilizedFinePointSourceSolution
        4 L j mass a z sourceEndpoint m
  have hsplit := Finset.sum_erase_add
    (Finset.univ : Finset (CMP89Eq246AliasIndex 4 L j)) term
    (Finset.mem_univ central)
  rw [cmp89Eq246DirectedFullSolutionSum,
    cmp89Eq246DirectedNoncentralSolutionSum,
    cmp89Eq246StabilizedFineToFineGreenIntegrand]
  change term central +
      (∑ m ∈ (Finset.univ : Finset
        (CMP89Eq246AliasIndex 4 L j)).erase central, term m) =
    ∑ m : CMP89Eq246AliasIndex 4 L j, term m
  simpa [add_comm] using hsplit

/-- Consequently the normalized directed synthesis is the normalized
integral of the complete point-source integrand on the selected contour. -/
theorem cmp89Eq246DirectedNormalizedFullSolutionIntegral_eq_signedContour
    (L j : ℕ) [NeZero L] (mass a rho : ℝ)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ) :
    cmp89Eq246DirectedNormalizedFullSolutionIntegral
        L j mass a rho targetEndpoint sourceEndpoint =
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
        cmp89Eq246StabilizedFineToFineGreenIntegrand 4 L j mass a
          (cmp89Eq251SignedContourMomentum rho
            (cmp89Eq251PhysicalBrillouinParameter x)
            (fun mu => targetEndpoint mu - sourceEndpoint mu))
          targetEndpoint sourceEndpoint := by
  unfold cmp89Eq246DirectedNormalizedFullSolutionIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  exact cmp89Eq246DirectedFullSolutionSum_eq_signedContourIntegrand
    L j mass a rho (cmp89Eq251PhysicalBrillouinParameter x)
      targetEndpoint sourceEndpoint

/-- At radius zero the directed synthesis is exactly the already constructed
real-slice complete point-source inverse transform.  This is an equality of
the two Fourier presentations, not an inverse-uniqueness or periodization
claim. -/
theorem cmp89Eq246DirectedNormalizedFullSolutionIntegral_zero_eq_realSlice
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ) :
    cmp89Eq246DirectedNormalizedFullSolutionIntegral
        L j mass a 0 targetEndpoint sourceEndpoint =
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
        cmp89Eq246StabilizedFineToFineGreenIntegrand 4 L j mass a
          (fun mu =>
            (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
          targetEndpoint sourceEndpoint := by
  rw [cmp89Eq246DirectedNormalizedFullSolutionIntegral_eq_signedContour]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  funext mu
  simp [cmp89Eq251SignedContourMomentum]

end

end YangMills.RG
