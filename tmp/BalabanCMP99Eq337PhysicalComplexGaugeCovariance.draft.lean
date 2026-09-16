import YangMills.RG.BalabanCMP98ContourExponentialTransport
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedBackground

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.37): gauge covariance of the complex perturbation

The step-3 regional precision uses a local gauge representative of the
regular background.  The external perturbation in (3.37) must therefore be
transported by the same gauge action.  This module constructs that transport
and states the literal positive-bond covariance of `exp(i eta A') U`.

No tower or operator equality is accepted as an input.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- The complex-linear adjoint action agrees with matrix conjugation for the
physical matricial model, on the whole complexified fibre. -/
theorem cmp99SUNLieComplexCoordMatrixLM_adjoint
    (g : SUN Nc) (Z : SUNLieComplexCoord Nc) :
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SUNAdjointComplexActionLM
          (matrixSUNAdjointModel Nc) g Z) =
      g.val * cmp99SUNLieComplexCoordMatrixLM Nc Z * g.valᴴ := by
  change cmp99SUNLieComplexCoordMatrixLM Nc
      (cmp99SUNLieCoordComplexificationLM Nc
          ((matrixSUNAdjointModel Nc).adCLM g
            (cmp99SUNLieComplexCoordRealPart Z)) +
        Complex.I • cmp99SUNLieCoordComplexificationLM Nc
          ((matrixSUNAdjointModel Nc).adCLM g
            (cmp99SUNLieComplexCoordImagPart Z))) = _
  rw [map_add, map_smul,
    cmp99SUNLieComplexCoordMatrixLM_complexification,
    cmp99SUNLieComplexCoordMatrixLM_complexification,
    cmp98LieCoordMatrix_adCLM, cmp98LieCoordMatrix_adCLM]
  noncomm_ring

/-- Transport a complex perturbation one-cochain by the source-vertex gauge
action printed in CMP99 (3.28)--(3.30). -/
def cmp99Eq337PhysicalGaugeTransformComplexOneCochain
    (u : GaugeTransform d N (SUN Nc))
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc) :
    CMP99Eq337PhysicalComplexOneCochain d N Nc :=
  WithLp.toLp 2 fun b =>
    cmp99SUNAdjointComplexActionLM
      (matrixSUNAdjointModel Nc) (u b.1) (A b)

@[simp] theorem cmp99Eq337PhysicalGaugeTransformComplexOneCochain_apply
    (u : GaugeTransform d N (SUN Nc))
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (b : PhysicalBond d N) :
    cmp99Eq337PhysicalGaugeTransformComplexOneCochain u A b =
      cmp99SUNAdjointComplexActionLM
        (matrixSUNAdjointModel Nc) (u b.1) (A b) :=
  rfl

/-- Positive-bond covariance of the literal complex perturbation.  This is
the exact dictionary preventing an untransported `A'` from being applied to
the gauge-transformed baseline. -/
theorem cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix_gaugeAct
    (u : GaugeTransform d N (SUN Nc))
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N) :
    cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix
        (GaugeConfig.gaugeAct u U)
        (cmp99Eq337PhysicalGaugeTransformComplexOneCochain u A) eta b =
      u b.1 |>.val *
        cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix U A eta b *
          (u (b.1.shift b.2)).valᴴ := by
  rw [cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix,
    cmp99Eq337PrintedComplexGenerator_eq,
    cmp99Eq337PhysicalGaugeTransformComplexOneCochain_apply,
    cmp99SUNLieComplexCoordMatrixLM_adjoint,
    physicalMatrixExp_unitary_conj
      (specialUnitaryToUnitary (u b.1)),
    GaugeConfig.gaugeAct_apply]
  simp only [positiveEdgeOfPhysicalBond,
    FiniteLatticeGeometry.src, FiniteLatticeGeometry.dst]
  change u b.1 |>.val *
      physicalMatrixExp
        ((eta : ℂ) • cmp99SUNLieComplexCoordMatrixLM Nc (A b)) *
        (u b.1).valᴴ *
          ((u b.1).val * (U (positiveEdgeOfPhysicalBond b)).val *
            (u (b.1.shift b.2)).valᴴ) = _
  have hu : (u b.1).valᴴ * (u b.1).val = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self
        (specialUnitaryToUnitary (u b.1))
  rw [← mul_assoc (u b.1).valᴴ, hu, one_mul]
  noncomm_ring

end

end YangMills.RG
