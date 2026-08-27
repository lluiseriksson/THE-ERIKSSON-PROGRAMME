import YangMills.RG.BalabanCMP99Eq351PhysicalComplexOrientedPerturbation
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedBackground
import YangMills.RG.BalabanCMP116GaugeFixingMassDefect

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# CMP99 (3.51): unscaled divergence and source covariant adjoint of `A'`

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
    cmp99Eq337PhysicalComplexifyOneCochain_apply,
    cmp99SUNAdjointComplexAction_complexification]

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
