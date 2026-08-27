import YangMills.RG.BalabanCMP99Eq351PhysicalComplexOrientedPerturbation
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedBackground

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# CMP99 (3.51): canonical complex covariant divergence of `A'`

The diagonal source species is not supplied by a caller.  It is the literal
backward divergence of the same physical complex one-cochain and background
that define the oriented perturbation `A'`.  The second theorem identifies
that stencil with the sum of the outgoing and incoming oriented values, so
the later Laplacian regrouping cannot choose a separate diagonal field.
-/

namespace YangMills.RG

noncomputable section

variable {d N Nc : Nat} [NeZero d] [NeZero N] [NeZero Nc]

/-- Literal complex backward divergence appearing in the diagonal species of
CMP99 (3.51).  Both orientations are constructed from `U` and `A`. -/
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

/-- The divergence is exactly the sum of the canonical outgoing and incoming
oriented perturbations.  This is the source dictionary for `D_U^* A`; no
independent diagonal field occurs. -/
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

/-- Matrix presentation of the same internally constructed diagonal field.
The source regrouping is first proved at this level; chart-norm conversion is
reserved for Eq. (3.54). -/
def cmp99Eq351PhysicalComplexCovariantDivergenceMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (x : FinBox d N) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp99SUNLieComplexCoordMatrixLM Nc
    (cmp99Eq351PhysicalComplexCovariantDivergence U A x)

end

end YangMills.RG
