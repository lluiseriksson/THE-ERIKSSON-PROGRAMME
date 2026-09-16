import YangMills.RG.BalabanCMP99Eq337PhysicalComplexGaugeCovariance
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbationDomain

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.37): gauge transport of the physical real perturbation domain

The step-3 regional precision is written in the selected cube's gauge
representative, whereas (3.37) is stated for the original regular background.
This module transports the real one-cochain by the same source-vertex adjoint
action and derives covariance of the complete `(mu,nu)` tensor.  Consequently
membership in the two literal (3.37) bounds is transported rather than
reintroduced as a hypothesis.

No perturbed tower, averaging identity, Green operator or analytic estimate is
claimed here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- Source-vertex gauge transport of a real physical one-cochain.  The
physical matricial adjoint model is fixed internally. -/
noncomputable def cmp99Eq337PhysicalGaugeTransformRealOneCochain
    (u : GaugeTransform d N (SUN Nc))
    (A : PhysicalGaugeOneCochain d N Nc) :
    PhysicalGaugeOneCochain d N Nc :=
  WithLp.toLp 2 fun b =>
    (matrixSUNAdjointModel Nc).adCLM (u b.1) (A b)

@[simp] theorem cmp99Eq337PhysicalGaugeTransformRealOneCochain_apply
    (u : GaugeTransform d N (SUN Nc))
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d N) :
    cmp99Eq337PhysicalGaugeTransformRealOneCochain u A b =
      (matrixSUNAdjointModel Nc).adCLM (u b.1) (A b) :=
  rfl

/-- The complex transport already used for `exp(i eta A') U` restricts to
the real source-vertex transport. -/
theorem cmp99Eq337PhysicalGaugeTransformComplexOneCochain_complexification
    (u : GaugeTransform d N (SUN Nc))
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d N) :
    cmp99Eq337PhysicalGaugeTransformComplexOneCochain u
        (cmp99Eq337PhysicalComplexifyOneCochain A) b =
      cmp99SUNLieCoordComplexificationLM Nc
        (cmp99Eq337PhysicalGaugeTransformRealOneCochain u A b) := by
  rw [cmp99Eq337PhysicalGaugeTransformComplexOneCochain_apply,
    cmp99Eq337PhysicalComplexifyOneCochain_apply,
    cmp99SUNAdjointComplexAction_complexification]
  rfl

/-- Edgewise adjoint cancellation underlying covariance of the physical
covariant derivative. -/
theorem cmp99Eq337_adjoint_transport_edge
    (g0 g1 Ue : SUN Nc) (X : SUNLieCoord Nc) :
    (matrixSUNAdjointModel Nc).adCLM (g0 * Ue * g1⁻¹)
        ((matrixSUNAdjointModel Nc).adCLM g1 X) =
      (matrixSUNAdjointModel Nc).adCLM g0
        ((matrixSUNAdjointModel Nc).adCLM Ue X) := by
  rw [(matrixSUNAdjointModel Nc).ad_mul (g0 * Ue) g1⁻¹,
    ContinuousLinearMap.comp_apply,
    (matrixSUNAdjointModel Nc).ad_mul g0 Ue,
    ContinuousLinearMap.comp_apply,
    (matrixSUNAdjointModel Nc).ad_inv_apply_ad]

/-- The complete real tensor in (3.39) transforms at its source vertex.  This
is the named bridge required before the (3.37) domain may be fed to the
gauge-transformed regional precision. -/
theorem cmp99Eq337PhysicalRealCovariantDerivative_gaugeAct
    (u : GaugeTransform d N (SUN Nc))
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) (eta : ℝ)
    (x : FinBox d N) (mu nu : Fin d) :
    cmp99Eq337PhysicalRealCovariantDerivative
        (matrixSUNAdjointModel Nc) eta (GaugeConfig.gaugeAct u U)
        (cmp99Eq337PhysicalGaugeTransformRealOneCochain u A)
        (x, mu, nu) =
      (matrixSUNAdjointModel Nc).adCLM (u x)
        (cmp99Eq337PhysicalRealCovariantDerivative
          (matrixSUNAdjointModel Nc) eta U A (x, mu, nu)) := by
  rw [cmp99Eq337PhysicalRealCovariantDerivative_source_apply,
    cmp99Eq337PhysicalRealCovariantDerivative_source_apply]
  simp only [cmp99Eq337PhysicalGaugeTransformRealOneCochain_apply,
    GaugeConfig.gaugeAct_apply, positiveEdgeOfPhysicalBond,
    FiniteLatticeGeometry.src, FiniteLatticeGeometry.dst]
  rw [cmp99Eq337_adjoint_transport_edge]
  simp only [map_sub, map_smul]

end

section Domain

variable {L N' Nc n : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Nc] [NeZero n]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r ⇒ FinBox 4 (scaleExtent r))}

/-- Gauge covariance discharges the two (3.37) bounds for the transported
field and background.  The conclusion is not a new domain hypothesis: it is
constructed from the original source-domain witness. -/
theorem CMP99Eq337PhysicalRealPerturbationDomain.gaugeAct
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {A : PhysicalGaugeOneCochain 4 (L * N') Nc}
    {eta alpha1 : ℝ}
    (D : CMP99Eq337PhysicalRealPerturbationDomain
      (S := S) U A eta alpha1)
    (u : GaugeTransform 4 (L * N') (SUN Nc)) :
    CMP99Eq337PhysicalRealPerturbationDomain (S := S)
      (GaugeConfig.gaugeAct u U)
      (cmp99Eq337PhysicalGaugeTransformRealOneCochain u A)
      eta alpha1 := by
  refine {
    eta_pos := D.eta_pos
    alpha1_pos := D.alpha1_pos
    amplitude_bound := ?_
    covariant_derivative_bound := ?_ }
  · intro r x hx nu
    rw [cmp99Eq337PhysicalGaugeTransformRealOneCochain_apply,
      (matrixSUNAdjointModel Nc).norm_ad]
    exact D.amplitude_bound r x hx nu
  · intro r x hx mu nu
    rw [cmp99Eq337PhysicalRealCovariantDerivative_gaugeAct,
      (matrixSUNAdjointModel Nc).norm_ad]
    exact D.covariant_derivative_bound r x hx mu nu

end Domain

end YangMills.RG
