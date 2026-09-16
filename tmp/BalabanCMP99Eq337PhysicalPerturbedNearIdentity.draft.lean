import YangMills.RG.BalabanCMP98PhysicalSpecialUnitaryChart
import YangMills.RG.OrderedExponentialQuadraticBound
import YangMills.RG.SUNProductDeviation

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.37): near-identity radius of the physical perturbation

The source configuration is the literal left variation
`U'U = exp(eta A) * U`.  This leaf lemma keeps the two contributions to its
near-identity radius visible.  It assumes only the local generator and
baseline radii; the scale-indexed producer of those radii from (3.37) remains
a separate obligation.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The positive-bond value of the literal multiplicative perturbation has
radius `2 |eta| rA + rU`.  The two terms are not merged into an opaque
constant. -/
theorem norm_cmp98PhysicalSuLeftVariation_apply_pos_sub_one_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d (M * N')) (eta rA rU : ℝ)
    (hA : ‖((suLieCoordIso Nc).symm (A b)).toMatrix‖ ≤ rA)
    (hsmall : |eta| * rA ≤ 1 / 2)
    (hU : ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ rU) :
    ‖(cmp98PhysicalSuLeftVariation U A eta
          (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      2 * (|eta| * rA) + rU := by
  have hexp := norm_exp_smul_sub_one_le_two_mul eta rA
    ((suLieCoordIso Nc).symm (A b)).toMatrix hA hsmall
  have hproduct := norm_sun_mul_sub_one_le
    (cmp98PhysicalSuIncrement A b eta)
    (U (positiveEdgeOfPhysicalBond b))
  rw [show cmp98PhysicalSuLeftVariation U A eta
        (positiveEdgeOfPhysicalBond b) =
      cmp98PhysicalSuIncrement A b eta *
        U (positiveEdgeOfPhysicalBond b) by
    unfold cmp98PhysicalSuLeftVariation
    exact physicalLeftVariation_apply_pos _ _ _ _ _]
  exact hproduct.trans (add_le_add
    (by
      simpa only [cmp98PhysicalSuIncrement_coe, physicalMatrixExp] using
        hexp)
    hU)

end

end YangMills.RG
