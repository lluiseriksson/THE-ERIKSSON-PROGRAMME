import YangMills.RG.BalabanCMP89SourceNeumannGeneratedTwoScaleAbsorption
import YangMills.RG.BalabanCMP89SourceNeumannPhysicalGateReachability

/-!
# Reached generated two-scale CMP89 Neumann gate

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

The positive-radius scalar witness is consumed by the generated two-scale
physical absorption theorem.  The result remains depth two: it does not
construct a depth-uniform retained-tower Poincare theorem, CMP89 (2.42), or
window 15.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {N Nc : ℕ} [NeZero N] [NeZero Nc]

/-- At every fixed admissible physical spacing there is a positive source
radius and a literal closed two-step radius budget for which the generated
two-scale Neumann absorption theorem consumes the physical kernel equations.
-/
theorem exists_pos_cmp89SourceNeumann_generatedTwoScale_physical_absorption_radius
    (spacing : ℝ) (hspacing : 0 < spacing)
    (hnext : |(4 : ℝ) * spacing| ≤ 1) :
    ∃ epsilon : ℝ,
      ∃ budget : CMP99SourceUbarClosedBudget 4 4 Nc 2 epsilon,
        0 < epsilon ∧
        ∀ (Omega : ActiveGaugeRegion 4 N)
          (background :
            PhysicalGaugeBackground 4 (cmp99RegionalLatticeSize 4 N 2) Nc)
          (fineSmall :
            ∀ e : ConcreteEdge 4 (cmp99RegionalLatticeSize 4 N 2),
              ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
          (phi : ActiveGaugeZeroCochain
            (cmp99IteratedLiftActiveRegion (M := 4) Omega 2)
            (SUNLieCoord Nc))
          (hD : cmp89SourceNeumannRegionalCovariantD0CLM
            (cmp99IteratedLiftActiveRegion (M := 4) Omega 2)
            (matrixSUNAdjointModel Nc) background spacing phi = 0)
          (hQ :
            let Omega2 := cmp99IteratedLiftActiveRegion (M := 4) Omega 2
            let Scale : CMP99SourceNormalizedRegionalScale Omega2 background :=
              CMP99SourceNormalizedRegionalScale.ofFineSmall
                (by norm_num) (by norm_num) Omega2 background
                (cmp99IteratedLiftActiveRegion_blockSaturated Omega 1)
                epsilon budget.toRadiusChain.epsilon_nonneg
                budget.toRadiusChain.head_noWinding fineSmall
            cmp99SourceTransportedBlockAverageCLM
                (cmp99ActiveCoarseRegion (M := 4) (N' := 4 * N) Omega2)
                (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc)
                  Scale.toSourceScale.data.nextBackground)
                (cmp99SourceTransportedBlockAverageCLM Omega2
                  (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc)
                    background) phi) = 0),
          phi = 0 := by
  obtain ⟨epsilon, hepsilon, budget, hgate⟩ :=
    exists_pos_cmp89SourceNeumann_twoScale_physical_gate_radius
      (Nc := Nc) spacing hspacing
  refine ⟨epsilon, budget, hepsilon, ?_⟩
  intro Omega background fineSmall phi hD hQ
  exact eq_zero_of_cmp89SourceNeumann_generatedTwoScale_physical_absorption
    (d := 4) (M := 4) (N := N) (Nc := Nc)
    (by norm_num) (by norm_num) Omega hspacing budget.toRadiusChain
    background fineSmall hnext phi hD hQ hgate

end

end YangMills.RG
