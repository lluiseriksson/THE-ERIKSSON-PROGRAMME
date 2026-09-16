import YangMills.RG.BalabanCMP99Eq337PhysicalComplexCovariantDerivative

/-!
# CMP99 (3.50)--(3.51): canonical oriented complex perturbation

The source field is stored on positive physical bonds, while the printed
Laplacian expansion uses the oriented value `A'(b)`.  This module constructs
that value internally.  Positive edges read the supplied coordinate; negative
edges use the same background transport as the physical reversal convention,
including its minus sign.  No oriented family is accepted from the caller.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Complex-linear extension of the physical oriented one-cochain convention.
This is the literal source `A'` used in (3.50)--(3.52). -/
noncomputable def cmp99Eq351PhysicalComplexOrientedPerturbation
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (e : ConcreteEdge d N) : SUNLieComplexCoord Nc :=
  if e.sign then
    A (physicalBondOfEdge e)
  else
    -cmp99SUNAdjointComplexActionLM
      (matrixSUNAdjointModel Nc) (U e) (A (physicalBondOfEdge e))

@[simp] theorem cmp99Eq351PhysicalComplexOrientedPerturbation_pos
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (x : FinBox d N) (i : Fin d) :
    cmp99Eq351PhysicalComplexOrientedPerturbation U A
        (ConcreteEdge.mk x i true) = A (x, i) := by
  simp [cmp99Eq351PhysicalComplexOrientedPerturbation]

@[simp] theorem cmp99Eq351PhysicalComplexOrientedPerturbation_neg
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (x : FinBox d N) (i : Fin d) :
    cmp99Eq351PhysicalComplexOrientedPerturbation U A
        (ConcreteEdge.mk x i false) =
      -cmp99SUNAdjointComplexActionLM
        (matrixSUNAdjointModel Nc) (U (ConcreteEdge.mk x i false))
          (A (x, i)) := by
  simp [cmp99Eq351PhysicalComplexOrientedPerturbation]

/-- On real perturbations the complex source orientation is exactly the
complexification of the already sealed physical orientation convention. -/
theorem cmp99Eq351PhysicalComplexOrientedPerturbation_realSlice
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    cmp99Eq351PhysicalComplexOrientedPerturbation U
        (cmp99Eq337PhysicalComplexifyOneCochain A) e =
      cmp99SUNLieCoordComplexificationLM Nc
        (orientedOneValue (matrixSUNAdjointModel Nc) U A e) := by
  cases e with
  | mk x i sign =>
      cases sign with
      | false =>
          simp [cmp99Eq351PhysicalComplexOrientedPerturbation,
            orientedOneValue]
          change
            cmp99SUNAdjointComplexAction (matrixSUNAdjointModel Nc)
                (U.toFun { source := x, dir := i, sign := false })
                (cmp99SUNLieCoordComplexificationLM Nc (A.ofLp (x, i))) =
              cmp99SUNLieCoordComplexificationLM Nc
                ((matrixSUNAdjointModel Nc).adCLM
                  (U.toFun { source := x, dir := i, sign := false })
                  (A.ofLp (x, i)))
          exact cmp99SUNAdjointComplexAction_complexification
            (matrixSUNAdjointModel Nc)
            (U.toFun { source := x, dir := i, sign := false })
            (A.ofLp (x, i))
      | true =>
          simp [cmp99Eq351PhysicalComplexOrientedPerturbation,
            orientedOneValue]

end

end YangMills.RG
