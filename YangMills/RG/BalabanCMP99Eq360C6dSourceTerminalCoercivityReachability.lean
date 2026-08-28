import YangMills.RG.BalabanCMP99SourcePoincarePositiveRadiusReachability
import YangMills.RG.BalabanCMP99Eq360C6dSourceTerminalCoercivity

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Reachability of the literal C6d source coercivity package

This wrapper constructs one positive `alpha1`, one nonempty `alpha0` interval,
the closed retained-radius budget and the terminal Poincare absorption gate.
For every physical regularity witness whose `alpha0` lies in that interval it
then derives the Corollary-3.6 scale inequality and the literal C6d baseline
coercivity theorem.

The physical regularity witness itself remains an explicit source-facing
premise.  In particular this theorem does not rename the existence of a CMP99
regular background as a scalar smallness hypothesis.
-/

namespace YangMills.RG

noncomputable section

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

variable {L N' M Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero N'] [NeZero M] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}
variable {U : PhysicalGaugeBackground 4 (L * N') Nc}
variable {eta : ℝ}
variable (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge
  scaleExtent S scaleExtent_pos)
variable {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
variable (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
variable (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
variable (hM : 2 ≤ M) (hdepth : 0 < depth)

include hdepth

/-- A single constructed scalar package makes the literal positive-depth C6d
baseline precision coercive for every physical CMP99 regularity witness in the
resulting `alpha0` interval.  The operator, coefficient and coercivity floor are
all the source-fixed definitions; only the physical regularity witness remains
caller data. -/
theorem exists_pos_cmp99Eq360C6dSourceTerminalCoercivityInterval :
    ∃ alpha1 alpha0Radius : ℝ,
      0 < alpha1 ∧
      0 < alpha0Radius ∧
      ∃ halpha1 : alpha1 ≤ 1 / 2,
      ∃ baselineRadiusBudget : CMP99SourceUbarClosedBudget 4 M Nc depth
          (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1),
        cmp99SourcePoincareErrorCoeff 4 M depth eta
            (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1 ∧
        ∀ {alpha0 : ℝ}
            (R : CMP99Eq335PhysicalRegularityClass
              (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
              (scaleExtent := scaleExtent) (S := S)
              (scaleExtent_pos := scaleExtent_pos) U eta alpha0),
          0 ≤ alpha0 → alpha0 ≤ alpha0Radius →
          ∃ hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1,
            let W := R.toCubeWitness C alpha1 hscale
            let T := cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
              R C hscale regions D hM halpha1 baselineRadiusBudget
            let b := cmp99Eq360C6dSourcePhysicalCountingCoefficient
              R C hscale regions D hM halpha1 baselineRadiusBudget
            IsCoerciveCLM
              (cmp99SourceGaugePrecision
                (cmp99ActiveRegionSourceCovariantLaplacian Omega
                  (matrixSUNAdjointModel Nc) W.transformedBackground eta)
                T.Qprime b)
              (cmp99Eq360C6dSourceBaselinePhysicalCoercivity
                R C hscale regions D hM halpha1
                  baselineRadiusBudget) := by
  obtain ⟨alpha1, alpha0Radius, halpha1, halpha1_half,
      halpha0Radius, hbudget, hsmall, _hpivotRadius, _hpivotBudget,
      _hflat, hscaleRange⟩ :=
    exists_pos_poincare_sourceAlphaInterval
      (d := 4) (M := M) (N := L * N') (Nc := Nc) C depth eta
  refine ⟨alpha1, alpha0Radius, halpha1, halpha0Radius,
    halpha1_half, hbudget, hsmall, ?_⟩
  intro alpha0 R halpha0_nonneg halpha0_le
  let hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1 :=
    hscaleRange halpha0_nonneg halpha0_le
  refine ⟨hscale, ?_⟩
  dsimp only
  exact isCoerciveCLM_cmp99Eq360C6dSourceBaselinePrecision
    R C hscale regions D hM halpha1_half hbudget
    hdepth R.eta_pos hsmall

end

end YangMills.RG
