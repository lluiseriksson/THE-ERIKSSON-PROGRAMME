import YangMills.RG.BalabanCMP89SourceNeumannRecursivePoincareCoefficient
import YangMills.RG.BalabanCMP89SourceNeumannPhysicalDerivativeFeedback
import YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge

/-!
# Finite-depth physical CMP89 Neumann Poincare induction

PRE-VALIDATION: source present; `.olean` not yet materialized in a fresh
checkout, and the result has not yet been verified by the compiler.

This module installs the one-scale Neumann Poincare producer and the literal
physical derivative-feedback estimate at every member of one typed generated
`Ubar` chain.  The caller supplies one recursive scalar contraction budget,
not a family of backgrounds, operators, or Poincare certificates.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Physical spacing after `level` literal order-`M` coarse steps. -/
def cmp89SourceNeumannPhysicalSpacingAt (M : ℕ) (spacing : ℝ) : ℕ → ℝ
  | 0 => spacing
  | level + 1 => (M : ℝ) *
      cmp89SourceNeumannPhysicalSpacingAt M spacing level

@[simp] theorem cmp89SourceNeumannPhysicalSpacingAt_zero
    (M : ℕ) (spacing : ℝ) :
    cmp89SourceNeumannPhysicalSpacingAt M spacing 0 = spacing := rfl

@[simp] theorem cmp89SourceNeumannPhysicalSpacingAt_succ
    (M : ℕ) (spacing : ℝ) (level : ℕ) :
    cmp89SourceNeumannPhysicalSpacingAt M spacing (level + 1) =
      (M : ℝ) * cmp89SourceNeumannPhysicalSpacingAt M spacing level := rfl

/-- The one-scale coefficient at the physical spacing of `level`. -/
noncomputable def cmp89SourceNeumannPhysicalOneScaleCoefficientAt
    (d M : ℕ) (spacing : ℝ) (level : ℕ) : ℝ :=
  cmp89SourceNeumannOneScalePoincareConstant d M
    (cmp89SourceNeumannPhysicalSpacingAt M spacing level)

/-- The exact derivative coefficient is scale independent. -/
noncomputable def cmp89SourceNeumannPhysicalDerivativeCoefficientAt
    (d M : ℕ) (_level : ℕ) : ℝ :=
  cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient d M

/-- The exact field-feedback coefficient at adjacent generated radii. -/
noncomputable def cmp89SourceNeumannPhysicalFeedbackCoefficientAt
    (d M : ℕ) (spacing epsilon : ℝ) (level : ℕ) : ℝ :=
  cmp89SourceNeumannPhysicalFieldFeedbackCoefficient d M
    (cmp99SourceUbarRadiusAt d M epsilon level /
      cmp89SourceNeumannPhysicalSpacingAt M spacing level)
    (cmp99SourceUbarRadiusAt d M epsilon (level + 1) /
      cmp89SourceNeumannPhysicalSpacingAt M spacing (level + 1))

/-- A single recursive scalar budget for the physical generated chain. -/
abbrev CMP89SourceNeumannPhysicalRecursiveContractionBudget
    (d M : ℕ) (spacing epsilon : ℝ) (level steps : ℕ) :=
  CMP89SourceNeumannRecursiveContractionBudget
    (cmp89SourceNeumannPhysicalOneScaleCoefficientAt d M spacing)
    (cmp89SourceNeumannPhysicalDerivativeCoefficientAt d M)
    (cmp89SourceNeumannPhysicalFeedbackCoefficientAt d M spacing epsilon)
    level steps

/-- Positivity of every physical spacing generated from a positive initial
spacing. -/
theorem cmp89SourceNeumannPhysicalSpacingAt_pos
    (hM : 2 ≤ M) {spacing : ℝ} (hspacing : 0 < spacing) (level : ℕ) :
    0 < cmp89SourceNeumannPhysicalSpacingAt M spacing level := by
  induction level with
  | zero => simpa using hspacing
  | succ level ih =>
      rw [cmp89SourceNeumannPhysicalSpacingAt_succ]
      exact mul_pos (by exact_mod_cast (show 0 < M from lt_of_lt_of_le (by omega) hM)) ih

/-- The finite-depth physical induction on a typed generated region chain.
Every coarse background, region, radius, average and Poincare certificate is
constructed internally.  The only non-geometric analytic input is the single
recursive scalar contraction budget. -/
theorem CMP99SourceActiveRegionChain.neumannPhysicalPoincare
    {N steps : ℕ} [NeZero N] {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega (steps + 1))
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (level : ℕ)
    (background : PhysicalGaugeBackground d N Nc)
    (chain : CMP99SourceUbarRadiusChain d M Nc (steps + 1)
      (cmp99SourceUbarRadiusAt d M epsilon level))
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99SourceUbarRadiusAt d M epsilon level)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      d M spacing epsilon level steps) :
    CMP89SourceNeumannRegionalPoincare Omega (matrixSUNAdjointModel Nc) background
      (regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
        (cmp89SourceNeumannPhysicalSpacingAt M spacing level)
        (cmp99SourceUbarRadiusAt d M epsilon level)
        background chain fineSmall).Qprime
      (cmp89SourceNeumannPhysicalSpacingAt M spacing level)
      (cmp89SourceNeumannRecursivePoincareCoefficient
        (cmp89SourceNeumannPhysicalOneScaleCoefficientAt d M spacing)
        (cmp89SourceNeumannPhysicalDerivativeCoefficientAt d M)
        (cmp89SourceNeumannPhysicalFeedbackCoefficientAt d M spacing epsilon)
        level steps) := by
  induction steps generalizing N Omega level with
  | zero =>
      cases regions with
      | @step N' depth _ Omega hOmega tail =>
          cases tail with
          | stop OmegaCoarse =>
              have hcurrentSpacing :
                  cmp89SourceNeumannPhysicalSpacingAt M spacing level ≠ 0 :=
                ne_of_gt (cmp89SourceNeumannPhysicalSpacingAt_pos hM hspacing level)
              simpa [CMP99SourceActiveRegionChain.weightedQprimeTower,
                CMP99SourceWeightedRegionalTower.step,
                CMP99SourceWeightedRegionalTower.stop,
                cmp89SourceNeumannRecursivePoincareCoefficient,
                cmp89SourceNeumannPhysicalOneScaleCoefficientAt] using
                (cmp89SourceNeumann_oneScale_quantitativePoincare
                  Omega hOmega (matrixSUNAdjointModel Nc) background
                  hcurrentSpacing)
  | succ steps ih =>
      cases regions with
      | @step N' depth _ Omega hOmega tail =>
          cases chain with
          | step _ currentRadius_nonneg noWinding logSmall tailChain =>
              cases budget with
              | step _ _ fine_pos derivative_nonneg feedback_small tailBudget =>
                  let currentRadius := cmp99SourceUbarRadiusAt d M epsilon level
                  let currentSpacing :=
                    cmp89SourceNeumannPhysicalSpacingAt M spacing level
                  let nextSpacing := (M : ℝ) * currentSpacing
                  let nextRadius := cmp99SourceUbarNextFineRadius d M currentRadius
                  let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
                    CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega
                      background hOmega currentRadius currentRadius_nonneg
                      noWinding fineSmall
                  let nextBackground := Scale.toSourceScale.data.nextBackground
                  have hcurrentSpacing_pos : 0 < currentSpacing := by
                    exact cmp89SourceNeumannPhysicalSpacingAt_pos hM hspacing level
                  have hnextSpacing_pos : 0 < nextSpacing := by
                    exact mul_pos (by exact_mod_cast
                      (show 0 < M from lt_of_lt_of_le (by omega) hM))
                      hcurrentSpacing_pos
                  have nextSmall : ∀ e : ConcreteEdge d N',
                      ‖(nextBackground e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
                        nextRadius := by
                    intro e
                    simpa [nextBackground, nextRadius, Scale,
                      CMP99SourceNormalizedRegionalScale.ofFineSmall,
                      CMP99SourceRegionalScale.ofFineSmall] using
                      norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
                        hd hM Omega background
                        (cmp99SourceBlockAverageWeight M d) currentRadius
                        currentRadius_nonneg noWinding logSmall fineSmall e
                  have hfineRadius :
                      currentSpacing * (currentRadius / currentSpacing) =
                        currentRadius := by
                    field_simp
                  have hcoarseRadius :
                      nextSpacing * (nextRadius / nextSpacing) = nextRadius := by
                    field_simp
                  have hfineNonneg : 0 ≤ currentRadius / currentSpacing :=
                    div_nonneg currentRadius_nonneg hcurrentSpacing_pos.le
                  have hcoarseNonneg : 0 ≤ nextRadius / nextSpacing :=
                    div_nonneg tailChain.epsilon_nonneg hnextSpacing_pos.le
                  have coarsePoincare := ih tail hd hM hspacing (level + 1)
                    nextBackground tailChain nextSmall tailBudget
                  apply cmp89SourceNeumannRegionalPoincare_twoLevel_of_derivative_feedback
                    Omega
                    (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
                    (matrixSUNAdjointModel Nc) background nextBackground
                    (cmp99SourceTransportedBlockAverageCLM Omega
                      (cmp99SourceWeightedPhysicalTransport
                        (matrixSUNAdjointModel Nc) background))
                    (tail.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
                      nextSpacing nextRadius nextBackground tailChain
                      nextSmall).Qprime
                    currentSpacing nextSpacing
                    (cmp89SourceNeumannPhysicalOneScaleCoefficientAt
                      d M spacing level)
                    (cmp89SourceNeumannRecursivePoincareCoefficient
                      (cmp89SourceNeumannPhysicalOneScaleCoefficientAt d M spacing)
                      (cmp89SourceNeumannPhysicalDerivativeCoefficientAt d M)
                      (cmp89SourceNeumannPhysicalFeedbackCoefficientAt
                        d M spacing epsilon)
                      (level + 1) steps)
                    (cmp89SourceNeumannPhysicalDerivativeCoefficientAt d M level)
                    (cmp89SourceNeumannPhysicalFeedbackCoefficientAt
                      d M spacing epsilon level)
                  · exact fine_pos.le
                  · exact
                      (cmp89SourceNeumannRecursivePoincareCoefficient_pos
                        tailBudget).le
                  · exact derivative_nonneg
                  · simpa [currentSpacing,
                      cmp89SourceNeumannPhysicalOneScaleCoefficientAt] using
                      (cmp89SourceNeumann_oneScale_quantitativePoincare
                        Omega hOmega (matrixSUNAdjointModel Nc) background
                        (ne_of_gt hcurrentSpacing_pos))
                  · simpa [currentSpacing, nextSpacing, nextRadius,
                      cmp89SourceNeumannPhysicalSpacingAt_succ,
                      cmp99SourceUbarRadiusAt_succ] using coarsePoincare
                  · intro phi
                    simpa [currentSpacing, nextSpacing, currentRadius,
                        nextRadius, cmp89SourceNeumannPhysicalDerivativeCoefficientAt,
                        cmp89SourceNeumannPhysicalFeedbackCoefficientAt,
                        cmp89SourceNeumannPhysicalSpacingAt_succ,
                        cmp99SourceUbarRadiusAt_succ, hfineRadius,
                        hcoarseRadius] using
                      (norm_cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_sq_le_physical_feedback
                        Omega hOmega background nextBackground
                        hcurrentSpacing_pos phi
                        (currentRadius / currentSpacing)
                        (nextRadius / nextSpacing)
                        hfineNonneg hcoarseNonneg
                        (by
                          intro e
                          simpa [hfineRadius] using fineSmall e)
                        (by
                          intro b
                          simpa [hcoarseRadius] using
                            nextSmall (positiveEdgeOfPhysicalBond b)))
                  · exact feedback_small

/-- Canonical finite-depth endpoint: the internally generated terminal
average is the same `Q'` as the last retained physical prefix. -/
theorem cmp89SourceNeumann_generatedRetainedFiniteDepthPhysicalPoincare
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N)
    (steps : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : PhysicalGaugeBackground d
      (cmp99RegionalLatticeSize M N (steps + 1)) Nc)
    (chain : CMP99SourceUbarRadiusChain d M Nc (steps + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
        (cmp99RegionalLatticeSize M N (steps + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      d M spacing epsilon 0 steps) :
    let T := cmp99SourceGeneratedRetainedPhysicalTower hd hM
      (matrixSUNAdjointModel Nc) Omega
      (steps + 1) spacing epsilon background chain fineSmall
    CMP89SourceNeumannRegionalPoincare
      (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
      (matrixSUNAdjointModel Nc) background
      (T.towerAt (Fin.last (steps + 1))).Qprime spacing
      (cmp89SourceNeumannRecursivePoincareCoefficient
        (cmp89SourceNeumannPhysicalOneScaleCoefficientAt d M spacing)
        (cmp89SourceNeumannPhysicalDerivativeCoefficientAt d M)
        (cmp89SourceNeumannPhysicalFeedbackCoefficientAt d M spacing epsilon)
        0 steps) := by
  dsimp only
  rw [cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower
    hd hM (matrixSUNAdjointModel Nc) Omega (steps + 1) spacing epsilon
      background chain fineSmall]
  simpa using
    (CMP99SourceActiveRegionChain.neumannPhysicalPoincare
      (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (steps + 1))
      hd hM hspacing 0 background chain fineSmall budget)

end

end YangMills.RG
