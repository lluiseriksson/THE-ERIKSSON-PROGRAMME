import YangMills.RG.BalabanCMP99Eq337PhysicalPerturbedNearIdentity
import YangMills.RG.BalabanCMP99Eq337PhysicalRealPerturbationDomain
import YangMills.RG.BalabanCMP116WilsonPlaquetteEnergy

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.37): real-domain input to the perturbed near-identity bound

This wrapper consumes the literal amplitude clause of the physical real
perturbation domain at one source scale.  It derives the matrix generator
bound internally and feeds the already separated product estimate for
`exp(eta A) U`.

The baseline radius and the scalar exponential window remain visible.  No
complexified (3.37) conclusion is claimed.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {L N' Nc n : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Nc] [NeZero n]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}

/-- The real-slice (3.37) amplitude bound supplies the generator radius in
the literal multiplicative perturbation at one positive physical bond. -/
theorem norm_cmp98PhysicalSuLeftVariation_apply_pos_sub_one_le_of_eq337
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (A : PhysicalGaugeOneCochain 4 (L * N') Nc)
    (eta alpha1 rU : ℝ)
    (D : CMP99Eq337PhysicalRealPerturbationDomain
      (S := S) U A eta alpha1)
    (r : Fin n) (b : PhysicalBond 4 (L * N'))
    (hb : b.1 ∈ S.global.regions r.castSucc)
    (halpha1 : alpha1 ≤ 1 / 2)
    (hU : ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ rU) :
    ‖(cmp98PhysicalSuLeftVariation U A eta
          (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      2 * (|eta| *
        cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1) + rU := by
  let X : SuLie Nc := (suLieCoordIso Nc).symm (A b)
  have hX : ‖X.toMatrix‖ ≤
      cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1 := by
    calc
      ‖X.toMatrix‖ ≤ ‖X‖ := norm_suLie_toMatrix_l2_opNorm_le X
      _ = ‖A b‖ := by
        exact (suLieCoordIso Nc).symm.norm_map _
      _ ≤ cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1 :=
        (D.amplitude_bound_at r b.1 hb b.2).le
  have hsmall : |eta| *
      cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1 ≤ 1 / 2 :=
    (D.abs_eta_mul_amplitudeMajorant_le r).trans halpha1
  exact norm_cmp98PhysicalSuLeftVariation_apply_pos_sub_one_le
    U A b eta
      (cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1) rU
      hX hsmall hU

end

end YangMills.RG
