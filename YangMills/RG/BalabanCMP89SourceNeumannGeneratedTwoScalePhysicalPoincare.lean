import YangMills.RG.BalabanCMP89SourceNeumannPhysicalDerivativeFeedback
import YangMills.RG.BalabanCMP99SourceRetainedPhysicalTower

/-!
# Generated depth-two physical CMP89 Neumann Poincare producer

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and no declaration below has yet been verified by the Lean compiler.

This module installs the literal physical derivative-feedback estimate on the
first two members of the source-generated `Ubar` tower.  The next background,
region and deviation radius are constructed internally.  The result remains
depth two and does not assert a depth-uniform retained-tower theorem.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The generated first `Ubar` background supplies every physical input of
the quantitative depth-two Neumann Poincare producer.  The only scalar input
left visible is its literal feedback contraction. -/
theorem cmp89SourceNeumann_generatedTwoScale_quantitativePoincare_of_physical_feedback
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (chain : CMP99SourceUbarRadiusChain d M Nc 2 epsilon)
    (background :
      PhysicalGaugeBackground d (cmp99RegionalLatticeSize M N 2) Nc)
    (fineSmall : ∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N 2),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (feedback_small :
      cmp89SourceNeumannOneScalePoincareConstant d M spacing *
          cmp89SourceNeumannOneScalePoincareConstant d M
            ((M : ℝ) * spacing) *
          cmp89SourceNeumannPhysicalFieldFeedbackCoefficient d M
            (epsilon / spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon /
              ((M : ℝ) * spacing)) < 1) :
    let Omega2 := cmp99IteratedLiftActiveRegion (M := M) Omega 2
    let Scale : CMP99SourceNormalizedRegionalScale Omega2 background :=
      CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega2 background
        (cmp99IteratedLiftActiveRegion_blockSaturated Omega 1)
        epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
    CMP89SourceNeumannRegionalPoincare
      Omega2 (matrixSUNAdjointModel Nc) background
      ((cmp99SourceTransportedBlockAverageCLM
          (cmp99ActiveCoarseRegion (M := M) (N' := M * N) Omega2)
          (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc)
            Scale.toSourceScale.data.nextBackground)).comp
        (cmp99SourceTransportedBlockAverageCLM Omega2
          (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc)
            background)))
      spacing
      (cmp89SourceNeumannTwoLevelPoincareConstant
        (cmp89SourceNeumannOneScalePoincareConstant d M spacing)
        (cmp89SourceNeumannOneScalePoincareConstant d M
          ((M : ℝ) * spacing))
        (cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient d M)
        (cmp89SourceNeumannPhysicalFieldFeedbackCoefficient d M
          (epsilon / spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon /
            ((M : ℝ) * spacing)))) := by
  dsimp only
  let Omega2 := cmp99IteratedLiftActiveRegion (M := M) Omega 2
  let Scale : CMP99SourceNormalizedRegionalScale Omega2 background :=
    CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega2 background
      (cmp99IteratedLiftActiveRegion_blockSaturated Omega 1)
      epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
  let nextBackground := Scale.toSourceScale.data.nextBackground
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hspacing0 : spacing ≠ 0 := ne_of_gt hspacing
  have hnextSpacing0 : (M : ℝ) * spacing ≠ 0 :=
    mul_ne_zero hM0 hspacing0
  have hOmega2 : Omega2.BlockSaturated :=
    cmp99IteratedLiftActiveRegion_blockSaturated Omega 1
  have hOmega1 :
      (cmp99ActiveCoarseRegion (M := M) (N' := M * N) Omega2).BlockSaturated := by
    rw [show cmp99ActiveCoarseRegion (M := M) (N' := M * N) Omega2 =
      cmp99IteratedLiftActiveRegion (M := M) Omega 1 by
        exact cmp99ActiveCoarseRegion_iteratedLift_succ_eq (M := M) Omega 1]
    exact cmp99IteratedLiftActiveRegion_blockSaturated Omega 0
  have nextSmall : ∀ e : ConcreteEdge d (M * N),
      ‖(nextBackground e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99SourceUbarNextFineRadius d M epsilon := by
    intro e
    simpa [nextBackground, Scale,
      CMP99SourceNormalizedRegionalScale.ofFineSmall,
      CMP99SourceRegionalScale.ofFineSmall] using
      norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
        hd hM Omega2 background (cmp99SourceBlockAverageWeight M d) epsilon
        chain.epsilon_nonneg chain.head_noWinding chain.head_logSmall fineSmall e
  have hfineRadius : spacing * (epsilon / spacing) = epsilon := by
    field_simp
  have hcoarseRadius :
      ((M : ℝ) * spacing) *
          (cmp99SourceUbarNextFineRadius d M epsilon /
            ((M : ℝ) * spacing)) =
        cmp99SourceUbarNextFineRadius d M epsilon := by
    field_simp
  have hfineNonneg : 0 ≤ epsilon / spacing :=
    div_nonneg chain.epsilon_nonneg hspacing.le
  have hcoarseNonneg : 0 ≤
      cmp99SourceUbarNextFineRadius d M epsilon /
        ((M : ℝ) * spacing) :=
    div_nonneg chain.tail.epsilon_nonneg
      (mul_nonneg (Nat.cast_nonneg M) hspacing.le)
  apply cmp89SourceNeumann_twoScale_quantitativePoincare_of_physical_feedback
    Omega2 hOmega2 hOmega1 background nextBackground hspacing
      (epsilon / spacing)
      (cmp99SourceUbarNextFineRadius d M epsilon /
        ((M : ℝ) * spacing))
      hfineNonneg hcoarseNonneg
  · intro e
    simpa [hfineRadius] using fineSmall e
  · intro b
    simpa [hcoarseRadius] using nextSmall (positiveEdgeOfPhysicalBond b)
  · simpa [Omega2, Scale, nextBackground] using feedback_small

/-- At every admissible physical spacing there is one positive source radius
whose internally generated two-step `Ubar` tower carries the quantitative
regional Neumann Poincare certificate.  The witness is common to every
finite source region and every background satisfying the literal radius
bound. -/
theorem exists_pos_cmp89SourceNeumann_generatedTwoScale_physicalPoincare_radius
    (spacing : ℝ) (hspacing : 0 < spacing)
    (hnextSpacing : |(4 : ℝ) * spacing| ≤ 1) :
    ∃ epsilon : ℝ,
      ∃ budget : CMP99SourceUbarClosedBudget 4 4 Nc 2 epsilon,
        0 < epsilon ∧
        ∀ (Omega : ActiveGaugeRegion 4 N)
          (background :
            PhysicalGaugeBackground 4 (cmp99RegionalLatticeSize 4 N 2) Nc)
          (fineSmall :
            ∀ e : ConcreteEdge 4 (cmp99RegionalLatticeSize 4 N 2),
              ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
          let Omega2 := cmp99IteratedLiftActiveRegion (M := 4) Omega 2
          let Scale : CMP99SourceNormalizedRegionalScale Omega2 background :=
            CMP99SourceNormalizedRegionalScale.ofFineSmall
              (by norm_num) (by norm_num) Omega2 background
              (cmp99IteratedLiftActiveRegion_blockSaturated Omega 1)
              epsilon budget.toRadiusChain.epsilon_nonneg
              budget.toRadiusChain.head_noWinding fineSmall
          CMP89SourceNeumannRegionalPoincare
            Omega2 (matrixSUNAdjointModel Nc) background
            ((cmp99SourceTransportedBlockAverageCLM
                (cmp99ActiveCoarseRegion (M := 4) (N' := 4 * N) Omega2)
                (cmp99SourceWeightedPhysicalTransport
                  (matrixSUNAdjointModel Nc)
                  Scale.toSourceScale.data.nextBackground)).comp
              (cmp99SourceTransportedBlockAverageCLM Omega2
                (cmp99SourceWeightedPhysicalTransport
                  (matrixSUNAdjointModel Nc) background)))
            spacing
            (cmp89SourceNeumannTwoLevelPoincareConstant
              (cmp89SourceNeumannOneScalePoincareConstant 4 4 spacing)
              (cmp89SourceNeumannOneScalePoincareConstant 4 4
                ((4 : ℝ) * spacing))
              (cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient 4 4)
              (cmp89SourceNeumannPhysicalFieldFeedbackCoefficient 4 4
                (epsilon / spacing)
                (cmp99SourceUbarNextFineRadius 4 4 epsilon /
                  ((4 : ℝ) * spacing)))) := by
  obtain ⟨epsilon, hepsilon, budget, hgate⟩ :=
    exists_pos_cmp89SourceNeumann_twoScale_physical_feedback_radius
      (Nc := Nc) spacing hspacing hnextSpacing
  refine ⟨epsilon, budget, hepsilon, ?_⟩
  intro Omega background fineSmall
  exact
    cmp89SourceNeumann_generatedTwoScale_quantitativePoincare_of_physical_feedback
      (d := 4) (M := 4) (N := N) (Nc := Nc)
      (by norm_num) (by norm_num) Omega hspacing budget.toRadiusChain
      background fineSmall hgate

end

end YangMills.RG
