import YangMills.RG.BalabanCMP85SourcePrefixGreen
import YangMills.RG.BalabanCMP89SourceNeumannRegionalPrecision

/-!
# CMP89 regional Neumann gauge precision and canonical Green

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and no result in this module is compiler-verified.

This module keeps the three terms of the operator printed in CMP89 (2.44)
separate:

`-Delta^xi + mass^2 + a Q_j^* Q_j`.

The first term is the internal-bond Neumann Laplacian fixed by
`BalabanCMP89SourceNeumannRegionalPrecision`; the bare mass is independent of
the flowing averaging coefficient; and `Qprime` remains visible in this
algebraic layer.  A source-facing consumer must instantiate it with the
retained physical `Q_j` from the same background tower.  The scalar `a` in
this counting-Hilbert presentation is likewise the coefficient of
`Qprime.adjoint.comp Qprime`; identifying it with the printed `a_j` requires
the already named source-weighted/counting-volume dictionary and is not
asserted here.

The canonical Green below is constructed as the inverse of this one
precision.  Its only analytic input is a named Neumann block-Poincare bound
for the same derivative and the same `Qprime`.  In particular, positivity of
the bare mass is neither assumed nor used to manufacture scale-uniform
coercivity.  This module does not construct that Poincare producer, identify
the source rectangle, or prove the multiple-reflection formula CMP89 (2.42).
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Literal three-term CMP89 regional Neumann precision. -/
noncomputable def cmp89SourceNeumannRegionalGaugePrecision
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass a : ℝ) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  cmp99SourceGaugePrecision
    (cmp85BareMassPrecision
      (cmp89SourceNeumannRegionalLaplacian Omega rho U spacing) mass)
    Qprime a

/-- Exact quadratic form with the Laplacian, bare mass and averaging
contributions still individually visible. -/
theorem inner_cmp89SourceNeumannRegionalGaugePrecision
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass a : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    inner ℝ phi
        (cmp89SourceNeumannRegionalGaugePrecision
          Omega rho U Qprime spacing mass a phi) =
      ‖cmp89SourceNeumannRegionalCovariantD0CLM
          Omega rho U spacing phi‖ ^ 2 +
        mass ^ 2 * ‖phi‖ ^ 2 + a * ‖Qprime phi‖ ^ 2 := by
  rw [cmp89SourceNeumannRegionalGaugePrecision,
    inner_cmp99SourceGaugePrecision,
    inner_cmp85BareMassPrecision,
    inner_cmp89SourceNeumannRegionalLaplacian]

/-- The literal three-term regional precision is self-adjoint. -/
theorem cmp89SourceNeumannRegionalGaugePrecision_isSymmetric
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass a : ℝ) :
    (cmp89SourceNeumannRegionalGaugePrecision
      Omega rho U Qprime spacing mass a).IsSymmetric := by
  apply cmp99SourceGaugePrecision_isSymmetric
  exact cmp85BareMassPrecision_isSymmetric _ _
    (cmp89SourceNeumannRegionalLaplacian_isSymmetric
      Omega rho U spacing)

/-- The one analytic gate needed to control the Neumann zero modes.  It uses
the same internal-bond derivative and the same averaging operator as the
literal precision. -/
def CMP89SourceNeumannRegionalPoincare
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing CP : ℝ) : Prop :=
  ∀ phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc),
    ‖phi‖ ^ 2 ≤ CP *
      (‖cmp89SourceNeumannRegionalCovariantD0CLM
          Omega rho U spacing phi‖ ^ 2 + ‖Qprime phi‖ ^ 2)

/-- A Neumann block-Poincare estimate makes the three-term precision
coercive with a floor independent of the bare mass. -/
theorem isCoerciveCLM_cmp89SourceNeumannRegionalGaugePrecision
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass : ℝ) {a CP : ℝ}
    (ha : 0 ≤ a) (hCP : 0 < CP)
    (hP : CMP89SourceNeumannRegionalPoincare
      Omega rho U Qprime spacing CP) :
    IsCoerciveCLM
      (cmp89SourceNeumannRegionalGaugePrecision
        Omega rho U Qprime spacing mass a)
      (min 1 a / CP) := by
  let D := cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
  let K := cmp85BareMassPrecision D mass
  have hKnonneg : ∀ phi, 0 ≤ inner ℝ phi (K phi) := by
    intro phi
    rw [K, inner_cmp85BareMassPrecision, D,
      inner_cmp89SourceNeumannRegionalLaplacian]
    positivity
  have hP' : ∀ phi, ‖phi‖ ^ 2 ≤
      CP * (inner ℝ phi (K phi) + ‖Qprime phi‖ ^ 2) := by
    intro phi
    calc
      ‖phi‖ ^ 2 ≤ CP *
          (‖cmp89SourceNeumannRegionalCovariantD0CLM
              Omega rho U spacing phi‖ ^ 2 + ‖Qprime phi‖ ^ 2) := hP phi
      _ ≤ CP * (inner ℝ phi (K phi) + ‖Qprime phi‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hCP.le
        rw [K, inner_cmp85BareMassPrecision, D,
          inner_cmp89SourceNeumannRegionalLaplacian]
        gcongr
        exact le_add_of_nonneg_right
          (mul_nonneg (sq_nonneg mass) (sq_nonneg ‖phi‖))
  simpa [cmp89SourceNeumannRegionalGaugePrecision, K, D] using
    (coercive_add_adjointMass_of_blockPoincare
      K Qprime ha hCP hKnonneg hP')

/-- Canonical regional Neumann Green generated from the literal precision;
no Green family is accepted from the caller. -/
noncomputable def cmp89SourceNeumannRegionalGreen
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass : ℝ) {a CP : ℝ}
    (ha : 0 < a) (hCP : 0 < CP)
    (hP : CMP89SourceNeumannRegionalPoincare
      Omega rho U Qprime spacing CP) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  covarianceOfIsCoerciveCLM
    (cmp89SourceNeumannRegionalGaugePrecision
      Omega rho U Qprime spacing mass a)
    (div_pos (lt_min zero_lt_one ha) hCP)
    (isCoerciveCLM_cmp89SourceNeumannRegionalGaugePrecision
      Omega rho U Qprime spacing mass ha.le hCP hP)

/-- Exact right inverse law for the generated Neumann Green. -/
theorem cmp89SourceNeumannRegionalGaugePrecision_comp_green
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass : ℝ) {a CP : ℝ}
    (ha : 0 < a) (hCP : 0 < CP)
    (hP : CMP89SourceNeumannRegionalPoincare
      Omega rho U Qprime spacing CP) :
    (cmp89SourceNeumannRegionalGaugePrecision
      Omega rho U Qprime spacing mass a).comp
        (cmp89SourceNeumannRegionalGreen
          Omega rho U Qprime spacing mass ha hCP hP) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) := by
  unfold cmp89SourceNeumannRegionalGreen
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (div_pos (lt_min zero_lt_one ha) hCP) _

/-- Exact left inverse law for the same generated Neumann Green. -/
theorem cmp89SourceNeumannRegionalGreen_comp_gaugePrecision
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass : ℝ) {a CP : ℝ}
    (ha : 0 < a) (hCP : 0 < CP)
    (hP : CMP89SourceNeumannRegionalPoincare
      Omega rho U Qprime spacing CP) :
    (cmp89SourceNeumannRegionalGreen
      Omega rho U Qprime spacing mass ha hCP hP).comp
        (cmp89SourceNeumannRegionalGaugePrecision
          Omega rho U Qprime spacing mass a) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) := by
  unfold cmp89SourceNeumannRegionalGreen
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (div_pos (lt_min zero_lt_one ha) hCP) _

end

end YangMills.RG
