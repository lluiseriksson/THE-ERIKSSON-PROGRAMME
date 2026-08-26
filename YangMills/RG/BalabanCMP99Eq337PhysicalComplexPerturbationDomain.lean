import YangMills.RG.BalabanCMP99Eq337PhysicalComplexCovariantDerivative
import YangMills.RG.BalabanCMP99Eq337PhysicalRealPerturbationDomain

/-!
# CMP99 (3.37): complex perturbation domain on the source regions

This is the literal complex-fibre counterpart of the physical real domain.
It uses one fine-lattice field on every nonterminal `Omega_j`, not a free
scale-indexed family.  The nonzero scale-count gate prevents vacuity.
The compact background action is fixed to `matrixSUNAdjointModel`; no
caller-selected adjoint representation is part of the physical domain.
-/

namespace YangMills.RG

noncomputable section

variable {L N' Nc n : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Nc] [NeZero n]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}

/-- Complex-fibre membership in the two perturbation bounds of (3.37). -/
structure CMP99Eq337PhysicalComplexPerturbationDomain
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain 4 (L * N') Nc)
    (eta alpha1 : ℝ) : Prop where
  eta_pos : 0 < eta
  alpha1_pos : 0 < alpha1
  amplitude_bound : ∀ r : Fin n,
    CMP99Eq337PhysicalComplexAmplitudeBoundOn
      (S.global.regions r.castSucc) A
      (cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1)
  covariant_derivative_bound : ∀ r : Fin n,
    CMP99Eq337PhysicalComplexCovariantDerivativeBoundOn
      (S.global.regions r.castSucc) (matrixSUNAdjointModel Nc) eta U A
      (cmp99Eq337PhysicalCovariantDerivativeMajorant
        L r.val eta alpha1)

end

end YangMills.RG
