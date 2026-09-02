import YangMills.RG.BalabanCMP89Eq246DirectedNormalizedPhysicalFineKernel
import YangMills.RG.BalabanCMP89Eq246FineToFineGreenProductContourTelescope

/-!
# PRE-VALIDATION: contour dictionary for the directed physical CMP89 (2.46) synthesis

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

The complete point-source telescope identifies the endpoint-selected directed
synthesis at radius `rho` with its real-slice value.  The consequence is an
exponential estimate for the literal real Fourier synthesis.  This still does
not identify that synthesis with a finite periodic/generated Green; that last
step belongs to the separate inverse-uniqueness dictionary.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- For literal fine-lattice endpoints, contour deformation identifies the
directed normalized synthesis at `rho` with the same synthesis at radius zero. -/
theorem cmp89Eq246DirectedNormalizedFullSolutionIntegral_physicalFine_eq_zero
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    cmp89Eq246DirectedNormalizedFullSolutionIntegral L j mass a rho
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) target)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) source) =
      cmp89Eq246DirectedNormalizedFullSolutionIntegral L j mass a 0
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) target)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) source) := by
  rw [cmp89Eq246DirectedNormalizedFullSolutionIntegral_eq_signedContour,
    cmp89Eq246DirectedNormalizedFullSolutionIntegral_zero_eq_realSlice]
  unfold cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
  congr 1
  simpa [cmp89Eq246PhysicalFineToFineGreenIntegrand] using
    (integral_cmp89Eq246PhysicalFineToFineGreenIntegrand_eq_signed
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hdenWindow hpairWindow hmass
      target source).symm

/-- The physical directed kernel is independent of the admissible contour
radius after the full-solver seam and telescope have been constructed. -/
theorem cmp89Eq246DirectedNormalizedPhysicalFineKernel_eq_zero
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    cmp89Eq246DirectedNormalizedPhysicalFineKernel
        L j mass a rho target source =
      cmp89Eq246DirectedNormalizedPhysicalFineKernel
        L j mass a 0 target source := by
  unfold cmp89Eq246DirectedNormalizedPhysicalFineKernel
  exact cmp89Eq246DirectedNormalizedFullSolutionIntegral_physicalFine_eq_zero
    ha hmassPos hrho hamplitude hradius hdenWindow hpairWindow hmass
      target source

/-- Exponential decay of the literal radius-zero physical fine-to-fine
Fourier synthesis, with the fine-lattice rate conversion visible. -/
theorem norm_cmp89Eq246NormalizedPhysicalFineToFineGreen_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    ‖cmp89Eq246NormalizedPhysicalFineToFineGreen
        L j mass a target source‖ ≤
      Real.exp (-((rho * cmp89Eq249FineLatticeSpacing L j) *
        cmp89Eq251LatticeL1Length (fun mu => target mu - source mu))) *
        cmp89Eq246DirectedFullSolutionSumBound L j a rho := by
  rw [← cmp89Eq246DirectedNormalizedPhysicalFineKernel_zero_eq_realGreenSynthesis]
  rw [← cmp89Eq246DirectedNormalizedPhysicalFineKernel_eq_zero
    ha hmassPos hrho hamplitude hradius hdenWindow hpairWindow hmass]
  exact norm_cmp89Eq246DirectedNormalizedPhysicalFineKernel_le
    ha hrho hradius hmass hdenWindow hpairWindow hamplitude target source

end

end YangMills.RG
