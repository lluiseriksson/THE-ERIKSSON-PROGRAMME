import YangMills.RG.FinitePiLpRealSliceFibreTransport
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier
import YangMills.RG.BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction

/-!
# PRE-VALIDATION: literal real point probe under the physical carrier map

Source present; .olean not materialized; result not compiler-verified.
This separate draft uses sealed definitions only, not the physical Green
draft currently being checked. It is not part of the active retry-v2 queue.

The input equality retains the entire Lie vector. No outer norm isometry,
Green identification, regional bound, derivative estimate or window-15
attainment is asserted. Counters remain 20/41 and TermSource = 0.
-/

namespace YangMills.RG

open YangMills
noncomputable section

/-- Canonical complexification of one real probe is the literal complex
point source, before changing the physical site coordinates. -/
theorem cmp99ComplexOuter_singleFinitePiLp_eq_pointSource_draft
    {d N Nc : ℕ} [NeZero N]
    (source : FinBox d N) (v : SUNLieCoord Nc) :
    finitePiLpComplexOuterEquiv
        (finitePiLpComplexOfReal (singleFinitePiLp source v)) =
      cmp99FlatComplexFibrePointSource source
        (cmp99SUNLieCoordComplexificationLM Nc v) := by
  classical
  funext target
  apply PiLp.ext
  intro k
  by_cases h : target = source
  · subst target
    simp [cmp99FlatComplexFibrePointSource, singleFinitePiLp,
      finitePiLpComplexOuterEquiv_apply, finitePiLpComplexOfReal_apply,
      cmp99SUNLieCoordComplexificationLM_apply]
  · simp [cmp99FlatComplexFibrePointSource, singleFinitePiLp, h,
      finitePiLpComplexOuterEquiv_apply, finitePiLpComplexOfReal_apply]

/-- The source is transported by the exact existing Step-7b equivalence;
the complexified vector is unchanged, not replaced by a basis probe. -/
theorem cmp99PhysicalStep7b_complexSingle_eq_pointSource_draft
    {L K Q Nc : ℕ} [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]
    (depth : ℕ)
    (source : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc) :
    cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
        (finitePiLpComplexOuterEquiv
          (finitePiLpComplexOfReal (singleFinitePiLp source v))) =
      cmp99FlatComplexFibrePointSource
        (cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth source)
        (cmp99SUNLieCoordComplexificationLM Nc v) := by
  classical
  rw [cmp99ComplexOuter_singleFinitePiLp_eq_pointSource_draft]
  let e := cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth
  funext y
  obtain ⟨x, hx⟩ := e.surjective y
  rw [← hx]
  have heval (f : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      SUNLieComplexCoord Nc) :
      cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
        f (e x) = f x := by
    simp [e, cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv,
      ContinuousLinearEquiv.piCongrLeft, Homeomorph.piCongrLeft,
      Equiv.piCongrLeft]
  rw [heval]
  change (if x = source then _ else _) =
    (if e x = e source then _ else _)
  simp only [e.injective.eq_iff]

#print axioms cmp99ComplexOuter_singleFinitePiLp_eq_pointSource_draft
#print axioms cmp99PhysicalStep7b_complexSingle_eq_pointSource_draft

end
end YangMills.RG
