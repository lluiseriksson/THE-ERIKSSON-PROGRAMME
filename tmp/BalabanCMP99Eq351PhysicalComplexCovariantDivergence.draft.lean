import YangMills.RG.BalabanCMP99Eq351PhysicalComplexOrientedPerturbation
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedBackground
import YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice
import YangMills.RG.BalabanCMP99SpecialUnitaryToSpecialLinearRealSlice
import YangMills.RG.BalabanCMP116GaugeFixingMassDefect
import tmp.BalabanCMP99Eq360ComplexRegionalLaplacian.draft

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# CMP99 (3.51): source covariant derivative and adjoint of `A'`

The diagonal source species is not supplied by a caller.  The unscaled
backward divergence is constructed from the same physical complex
one-cochain and background that define the oriented perturbation `A'`.  The
second theorem identifies that stencil with the sum of the outgoing and
incoming oriented values, so the later Laplacian regrouping cannot choose a
separate diagonal field.

CMP99 (3.3) uses the opposite derivative convention to the repository and
divides it by `eta`.  Therefore the printed adjoint `D_U^* A` is not the
unscaled divergence below: it is the separately named scalar multiple
`-eta^-1` of that divergence.  Keeping both objects visible prevents a silent
sign/spacing identification in the (3.51)--(3.53) regrouping.
-/

namespace YangMills.RG

noncomputable section

variable {d N Nc : Nat} [NeZero d] [NeZero N] [NeZero Nc]

/-- Literal complex source derivative `D_U^eta` from CMP99 (3.3), specialized
to the compact physical background.  Its orientation is fixed internally as
`eta^-1 * (R(U) phi_shift - phi)` rather than accepted from a caller. -/
def cmp99Eq351PhysicalComplexSourceCovariantDifference
    (U : PhysicalGaugeBackground d N Nc)
    (eta : ℝ)
    (phi : GaugeZeroCochain d N (SUNLieComplexCoord Nc))
    (b : PhysicalBond d N) : SUNLieComplexCoord Nc :=
  ((eta : ℂ)⁻¹) •
    (cmp99SpecialLinearAdjointCoordLM
        (cmp99SUNToSpecialLinear Nc
          (U (positiveEdgeOfPhysicalBond b)))
        (phi (b.1.shift b.2)) - phi b.1)

/-- Literal source derivative on an arbitrary oriented concrete edge.

Unlike the positive-bond storage type, `ConcreteEdge.source` is the anchor of
the underlying positive bond; the oriented endpoints are `srcV` and `dstV`.
Using those endpoints here is portante for the negative branch of the
two-orientation sum in CMP99 (3.50)--(3.51). -/
def cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference
    (U : PhysicalGaugeBackground d N Nc)
    (eta : ℝ)
    (phi : GaugeZeroCochain d N (SUNLieComplexCoord Nc))
    (e : ConcreteEdge d N) : SUNLieComplexCoord Nc :=
  ((eta : ℂ)⁻¹) •
    (cmp99SpecialLinearAdjointCoordLM
        (cmp99SUNToSpecialLinear Nc (U e)) (phi e.dstV) - phi e.srcV)

@[simp] theorem cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference_pos
    (U : PhysicalGaugeBackground d N Nc)
    (eta : ℝ)
    (phi : GaugeZeroCochain d N (SUNLieComplexCoord Nc))
    (x : FinBox d N) (i : Fin d) :
    cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference U eta phi
        (ConcreteEdge.mk x i true) =
      cmp99Eq351PhysicalComplexSourceCovariantDifference U eta phi (x, i) := by
  rfl

/-- The canonical negative edge leaving `x` is stored at `x.shiftBack i`.
This theorem exposes the actual source-facing endpoint order and the compact
reverse link; it is not inferred from the positive-bond formula. -/
@[simp] theorem cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference_neg
    (U : PhysicalGaugeBackground d N Nc)
    (eta : ℝ)
    (phi : GaugeZeroCochain d N (SUNLieComplexCoord Nc))
    (x : FinBox d N) (i : Fin d) :
    cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference U eta phi
        (ConcreteEdge.mk (x.shiftBack i) i false) =
      ((eta : ℂ)⁻¹) •
        (cmp99SpecialLinearAdjointCoordLM
            (cmp99SUNToSpecialLinear Nc
              (U (ConcreteEdge.mk (x.shiftBack i) i false)))
            (phi (x.shiftBack i)) - phi x) := by
  simp [cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference,
    ConcreteEdge.srcV, ConcreteEdge.dstV, FinBox.shift_shiftBack]

/-- Recovering the transported endpoint from the printed source derivative.
The nonzero-spacing premise is visible exactly at the cancellation step. -/
theorem cmp99Eq351PhysicalComplexOrientedSource_transport
    (U : PhysicalGaugeBackground d N Nc)
    (eta : ℝ) (heta : eta ≠ 0)
    (phi : GaugeZeroCochain d N (SUNLieComplexCoord Nc))
    (e : ConcreteEdge d N) :
    cmp99SpecialLinearAdjointCoordLM
        (cmp99SUNToSpecialLinear Nc (U e)) (phi e.dstV) =
      phi e.srcV + (eta : ℂ) •
        cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference
          U eta phi e := by
  have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta
  unfold cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference
  rw [smul_smul, mul_inv_cancel₀ hetaC, one_smul]
  module

/-- The analytic Eq360 stencil uses the repository's opposite covariant-
difference convention.  This named equality is the sign dictionary required
before its Laplacian expansion can be read as CMP99 (3.51). -/
theorem cmp99Eq351PhysicalComplexSourceCovariantDifference_eq_neg_repository
    (U : PhysicalGaugeBackground d N Nc)
    (eta : ℝ)
    (phi : GaugeZeroCochain d N (SUNLieComplexCoord Nc))
    (b : PhysicalBond d N) :
    cmp99Eq351PhysicalComplexSourceCovariantDifference U eta phi b =
      -cmp99Eq360ComplexCovariantDifference
        (cmp99PhysicalGaugeBackgroundToSpecialLinear U) eta phi b := by
  unfold cmp99Eq351PhysicalComplexSourceCovariantDifference
    cmp99Eq360ComplexCovariantDifference
  simp only [cmp99PhysicalGaugeBackgroundToSpecialLinear_apply]
  module

/-- Literal unscaled complex backward divergence.  Both orientations are
constructed from `U` and `A`; the printed source adjoint is defined below. -/
noncomputable def cmp99Eq351PhysicalComplexCovariantDivergence
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc) :
    GaugeZeroCochain d N (SUNLieComplexCoord Nc) :=
  WithLp.toLp 2 fun x =>
    ∑ i : Fin d,
      (A (x, i) -
        cmp99SUNAdjointComplexActionLM (matrixSUNAdjointModel Nc)
          (U (positiveEdgeOfPhysicalBond
            ((x.shiftBack i, i) : PhysicalBond d N)))⁻¹
          (A (x.shiftBack i, i)))

@[simp] theorem cmp99Eq351PhysicalComplexCovariantDivergence_apply
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (x : FinBox d N) :
    cmp99Eq351PhysicalComplexCovariantDivergence U A x =
      ∑ i : Fin d,
        (A (x, i) -
          cmp99SUNAdjointComplexActionLM (matrixSUNAdjointModel Nc)
            (U (positiveEdgeOfPhysicalBond
              ((x.shiftBack i, i) : PhysicalBond d N)))⁻¹
            (A (x.shiftBack i, i))) :=
  rfl

/-- The unscaled divergence is exactly the sum of the canonical outgoing and
incoming oriented perturbations.  No independent diagonal field occurs. -/
theorem cmp99Eq351PhysicalComplexCovariantDivergence_eq_sum_oriented
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (x : FinBox d N) :
    cmp99Eq351PhysicalComplexCovariantDivergence U A x =
      ∑ i : Fin d,
        (cmp99Eq351PhysicalComplexOrientedPerturbation U A
            (ConcreteEdge.mk x i true) +
          cmp99Eq351PhysicalComplexOrientedPerturbation U A
            (ConcreteEdge.mk (x.shiftBack i) i false)) := by
  rw [cmp99Eq351PhysicalComplexCovariantDivergence_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [cmp99Eq351PhysicalComplexOrientedPerturbation_pos,
    cmp99Eq351PhysicalComplexOrientedPerturbation_neg]
  have hU := U.map_reverse (ConcreteEdge.mk (x.shiftBack i) i true)
  change
    U (ConcreteEdge.mk (x.shiftBack i) i false) =
      (U (ConcreteEdge.mk (x.shiftBack i) i true))⁻¹ at hU
  rw [hU]
  rfl

/-- On the physical real slice the internally constructed unscaled complex
divergence is exactly the coordinate complexification of the sealed physical
gauge constraint.  No independently chosen complex diagonal field is
accepted. -/
theorem cmp99Eq351PhysicalComplexCovariantDivergence_realSlice
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) :
    cmp99Eq351PhysicalComplexCovariantDivergence U
        (cmp99Eq337PhysicalComplexifyOneCochain A) x =
      cmp99SUNLieCoordComplexificationLM Nc
        (gaugeConstraintQCLM (matrixSUNAdjointModel Nc) U A x) := by
  rw [cmp99Eq351PhysicalComplexCovariantDivergence_apply,
    gaugeConstraintQCLM_apply_background, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_sub, cmp99Eq337PhysicalComplexifyOneCochain_apply,
    cmp99Eq337PhysicalComplexifyOneCochain_apply]
  congr 1
  change
    cmp99SUNAdjointComplexAction (matrixSUNAdjointModel Nc)
        (U (positiveEdgeOfPhysicalBond ((x.shiftBack i, i) : PhysicalBond d N)))⁻¹
        (cmp99SUNLieCoordComplexificationLM Nc (A (x.shiftBack i, i))) =
      cmp99SUNLieCoordComplexificationLM Nc
        ((matrixSUNAdjointModel Nc).adCLM
          (U (positiveEdgeOfPhysicalBond ((x.shiftBack i, i) : PhysicalBond d N)))⁻¹
          (A (x.shiftBack i, i)))
  exact cmp99SUNAdjointComplexAction_complexification
    (matrixSUNAdjointModel Nc)
    (U (positiveEdgeOfPhysicalBond ((x.shiftBack i, i) : PhysicalBond d N)))⁻¹
    (A (x.shiftBack i, i))

/-- Literal source-facing complex adjoint `D_U^* A` from CMP99 (3.3)/(3.51).

The repository derivative `covariantD0CLM` is the negative of the printed
difference and lacks the printed factor `eta^-1`.  Its adjoint is therefore
`-eta^-1` times the unscaled backward divergence.  This definition fixes the
sign and scale internally; callers cannot supply a separate diagonal field or
an equality identifying one. -/
noncomputable def cmp99Eq351PhysicalComplexSourceCovariantAdjoint
    (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc) :
    GaugeZeroCochain d N (SUNLieComplexCoord Nc) :=
  (-((eta : ℂ)⁻¹)) • cmp99Eq351PhysicalComplexCovariantDivergence U A

@[simp] theorem cmp99Eq351PhysicalComplexSourceCovariantAdjoint_apply
    (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (x : FinBox d N) :
    cmp99Eq351PhysicalComplexSourceCovariantAdjoint eta U A x =
      (-((eta : ℂ)⁻¹)) •
        cmp99Eq351PhysicalComplexCovariantDivergence U A x :=
  rfl

/-- Source Eq. (3.8) written with the same two canonical oriented values that
enter the Laplacian expansion.  The visible negative inverse spacing is the
dictionary between the repository's oriented sum and the printed adjoint. -/
theorem cmp99Eq351PhysicalComplexSourceCovariantAdjoint_eq_smul_sum_oriented
    (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (x : FinBox d N) :
    cmp99Eq351PhysicalComplexSourceCovariantAdjoint eta U A x =
      (-((eta : ℂ)⁻¹)) •
        ∑ i : Fin d,
          (cmp99Eq351PhysicalComplexOrientedPerturbation U A
              (ConcreteEdge.mk x i true) +
            cmp99Eq351PhysicalComplexOrientedPerturbation U A
              (ConcreteEdge.mk (x.shiftBack i) i false)) := by
  rw [cmp99Eq351PhysicalComplexSourceCovariantAdjoint_apply,
    cmp99Eq351PhysicalComplexCovariantDivergence_eq_sum_oriented]

/-- Matrix presentation of the same internally constructed unscaled diagonal
field.  The source regrouping is first proved at this level; chart-norm
conversion is reserved for Eq. (3.54). -/
def cmp99Eq351PhysicalComplexCovariantDivergenceMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (x : FinBox d N) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp99SUNLieComplexCoordMatrixLM Nc
    (cmp99Eq351PhysicalComplexCovariantDivergence U A x)

end

end YangMills.RG
