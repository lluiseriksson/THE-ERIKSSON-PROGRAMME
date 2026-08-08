/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98ContourFirstVariation
import YangMills.RG.SUNAdjointMatrixSubstrate

/-!
# Ordered positive-contour transport in CMP98

The main line in CMP98 (124) is not obtained by merely naming the derivative
of the middle contour.  Its source form transports every bond generator to a
common basepoint.  This module isolates the exact ordered-product identity
that performs that transport.

For a positive Wilson line `W(t)` in the repository's left exponential chart,
the right-trivialized derivative `W'(0) W(0)ᴴ` is a recursively transported
sum of the bond generators.  No `g(ad)` inverse, small-field estimate, or
post-hoc remainder is introduced here.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Recursive prefix-transported generator sum of a positive contour. -/
def cmp98PositiveContourRightVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    List (ConcreteEdge d (M * N')) → Matrix (Fin Nc) (Fin Nc) ℂ
  | [] => 0
  | e :: es =>
      orientedWilsonGenerator A e +
        orientedWilsonFactor U A e 0 *
          cmp98PositiveContourRightVariation U A es *
            (orientedWilsonFactor U A e 0)ᴴ

/-- At zero chart parameter a positive oriented factor is its physical
special-unitary background matrix. -/
theorem orientedWilsonFactor_zero_of_pos
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) (he : e.sign = true) :
    orientedWilsonFactor U A e 0 = orientedWilsonPositiveBase U e := by
  simp [orientedWilsonFactor, he]

/-- The first variation of a positive oriented factor is the generator times
the background factor on the right. -/
theorem orientedWilsonFactorFirst_zero_of_pos
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) (he : e.sign = true) :
    orientedWilsonFactorFirst U A e 0 =
      orientedWilsonGenerator A e * orientedWilsonPositiveBase U e := by
  simp [orientedWilsonFactorFirst, he]

/-- Every positive background factor has the exact right-unitarity identity
used by the ordered transport calculation. -/
theorem orientedWilsonPositiveBase_mul_conjTranspose
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) :
    orientedWilsonPositiveBase U e * (orientedWilsonPositiveBase U e)ᴴ = 1 := by
  simpa only [orientedWilsonPositiveBase] using
    su_mul_conjTranspose_self
      (U (positiveEdgeOfPhysicalBond (physicalBondOfEdge e)))

/-- A positive contour evaluated at zero is unitary as an ordered matrix
product. -/
theorem cmp98ContourMatrixCurve_zero_mul_conjTranspose
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N')))
    (hpos : ∀ e ∈ es, e.sign = true) :
    cmp98ContourMatrixCurve U A es 0 *
        (cmp98ContourMatrixCurve U A es 0)ᴴ = 1 := by
  induction es with
  | nil => simp
  | cons e es ih =>
      have he : e.sign = true := hpos e (by simp)
      have hes : ∀ f ∈ es, f.sign = true := by
        intro f hf
        exact hpos f (by simp [hf])
      simp only [cmp98ContourMatrixCurve]
      rw [orientedWilsonFactor_zero_of_pos U A e he,
        Matrix.conjTranspose_mul]
      calc
        (orientedWilsonPositiveBase U e *
              cmp98ContourMatrixCurve U A es 0) *
            ((cmp98ContourMatrixCurve U A es 0)ᴴ *
              (orientedWilsonPositiveBase U e)ᴴ) =
            orientedWilsonPositiveBase U e *
              (cmp98ContourMatrixCurve U A es 0 *
                (cmp98ContourMatrixCurve U A es 0)ᴴ) *
              (orientedWilsonPositiveBase U e)ᴴ := by noncomm_ring
        _ = orientedWilsonPositiveBase U e *
              (orientedWilsonPositiveBase U e)ᴴ := by rw [ih hes, mul_one]
        _ = 1 := orientedWilsonPositiveBase_mul_conjTranspose U e

/-- **Exact ordered-path bridge.**  For a positive contour, right
trivialization of its genuine first variation is precisely the recursive
prefix-transported generator sum. -/
theorem cmp98ContourFirstVariation_mul_conjTranspose_eq_rightVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N')))
    (hpos : ∀ e ∈ es, e.sign = true) :
    cmp98ContourFirstVariation U A es 0 *
        (cmp98ContourMatrixCurve U A es 0)ᴴ =
      cmp98PositiveContourRightVariation U A es := by
  induction es with
  | nil => simp [cmp98PositiveContourRightVariation]
  | cons e es ih =>
      have he : e.sign = true := hpos e (by simp)
      have hes : ∀ f ∈ es, f.sign = true := by
        intro f hf
        exact hpos f (by simp [hf])
      simp only [cmp98ContourFirstVariation, cmp98ContourMatrixCurve,
        cmp98PositiveContourRightVariation, Matrix.conjTranspose_mul]
      rw [orientedWilsonFactor_zero_of_pos U A e he,
        orientedWilsonFactorFirst_zero_of_pos U A e he]
      have htail := cmp98ContourMatrixCurve_zero_mul_conjTranspose U A es hes
      have hbase := orientedWilsonPositiveBase_mul_conjTranspose U e
      calc
        ((orientedWilsonGenerator A e * orientedWilsonPositiveBase U e) *
              cmp98ContourMatrixCurve U A es 0 +
            orientedWilsonPositiveBase U e *
              cmp98ContourFirstVariation U A es 0) *
            ((cmp98ContourMatrixCurve U A es 0)ᴴ *
              (orientedWilsonPositiveBase U e)ᴴ) =
            orientedWilsonGenerator A e *
                (orientedWilsonPositiveBase U e *
                  (orientedWilsonPositiveBase U e)ᴴ) +
              orientedWilsonPositiveBase U e *
                (cmp98ContourFirstVariation U A es 0 *
                  (cmp98ContourMatrixCurve U A es 0)ᴴ) *
                (orientedWilsonPositiveBase U e)ᴴ := by
          calc
            _ = (orientedWilsonGenerator A e *
                    orientedWilsonPositiveBase U e) *
                  (cmp98ContourMatrixCurve U A es 0 *
                    (cmp98ContourMatrixCurve U A es 0)ᴴ) *
                  (orientedWilsonPositiveBase U e)ᴴ +
                orientedWilsonPositiveBase U e *
                  (cmp98ContourFirstVariation U A es 0 *
                    (cmp98ContourMatrixCurve U A es 0)ᴴ) *
                  (orientedWilsonPositiveBase U e)ᴴ := by noncomm_ring
            _ = _ := by rw [htail]; noncomm_ring
        _ = orientedWilsonGenerator A e +
              orientedWilsonPositiveBase U e *
                cmp98PositiveContourRightVariation U A es *
                (orientedWilsonPositiveBase U e)ᴴ := by
          rw [hbase, mul_one, ih hes]

/-- Matrix representative of one repository Lie-coordinate vector. -/
def cmp98LieCoordMatrix (X : SUNLieCoord Nc) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((suLieCoordIso Nc).symm X).toMatrix

@[simp] theorem cmp98LieCoordMatrix_zero :
    cmp98LieCoordMatrix (Nc := Nc) 0 = 0 := by
  simp only [cmp98LieCoordMatrix, map_zero]
  rfl

theorem cmp98LieCoordMatrix_add (X Y : SUNLieCoord Nc) :
    cmp98LieCoordMatrix (X + Y) =
      cmp98LieCoordMatrix X + cmp98LieCoordMatrix Y := by
  simp only [cmp98LieCoordMatrix, map_add]
  rfl

/-- The concrete adjoint model is literally matrix conjugation after the
orthonormal coordinate transport. -/
theorem cmp98LieCoordMatrix_adCLM
    (g : SUN Nc) (X : SUNLieCoord Nc) :
    cmp98LieCoordMatrix ((matrixSUNAdjointModel Nc).adCLM g X) =
      g.val * cmp98LieCoordMatrix X * g.valᴴ := by
  change
    ((suLieCoordIso Nc).symm
      ((suLieCoordIso Nc)
        (suAdActLin g ((suLieCoordIso Nc).symm X)))).toMatrix = _
  rw [(suLieCoordIso Nc).symm_apply_apply]
  rfl

/-- The physical special-unitary background attached to a positive physical
bond, packaged before forgetting to its matrix value. -/
def cmp98PositiveBaseSUN
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) : SUN Nc :=
  U (positiveEdgeOfPhysicalBond (physicalBondOfEdge e))

/-- Coordinate version of the prefix-transported generator sum. -/
def cmp98PositiveContourPrefixCoordinateSum
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    SUN Nc → List (ConcreteEdge d (M * N')) → SUNLieCoord Nc
  | _, [] => 0
  | pfx, e :: es =>
      (matrixSUNAdjointModel Nc).adCLM pfx
          (A (physicalBondOfEdge e)) +
        cmp98PositiveContourPrefixCoordinateSum U A
          (pfx * cmp98PositiveBaseSUN U e) es

/-- Exact coordinate/matrix dictionary for the recursively transported
positive-contour sum.  The prefix is kept explicit because CMP98 (125) uses
the block-basepoint-to-edge prefix holonomy. -/
theorem cmp98LieCoordMatrix_prefixCoordinateSum
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (pfx : SUN Nc) (es : List (ConcreteEdge d (M * N')))
    (hpos : ∀ e ∈ es, e.sign = true) :
    cmp98LieCoordMatrix
        (cmp98PositiveContourPrefixCoordinateSum U A pfx es) =
      pfx.val * cmp98PositiveContourRightVariation U A es * pfx.valᴴ := by
  induction es generalizing pfx with
  | nil => simp [cmp98PositiveContourPrefixCoordinateSum,
      cmp98PositiveContourRightVariation]
  | cons e es ih =>
      have he : e.sign = true := hpos e (by simp)
      have hes : ∀ f ∈ es, f.sign = true := by
        intro f hf
        exact hpos f (by simp [hf])
      rw [cmp98PositiveContourPrefixCoordinateSum,
        cmp98LieCoordMatrix_add, cmp98LieCoordMatrix_adCLM,
        ih (pfx := pfx * cmp98PositiveBaseSUN U e) hes]
      simp only [cmp98PositiveContourRightVariation,
        cmp98PositiveBaseSUN, orientedWilsonFactor_zero_of_pos U A e he,
        orientedWilsonPositiveBase]
      have hx : cmp98LieCoordMatrix (A (physicalBondOfEdge e)) =
          orientedWilsonGenerator A e := by
        simp [cmp98LieCoordMatrix, orientedWilsonGenerator,
          flatOrientedSuMatrixTangent, he]
      rw [hx]
      have hmul :
          ((pfx * U (positiveEdgeOfPhysicalBond
              (physicalBondOfEdge e)) : SUN Nc).val) =
            pfx.val *
              (U (positiveEdgeOfPhysicalBond
                (physicalBondOfEdge e))).val := rfl
      rw [hmul, Matrix.conjTranspose_mul]
      noncomm_ring

/-- Every edge of the literal straight source path is positively oriented. -/
theorem cmp99StraightPositivePath_edges_pos
    (x : FinBox d (M * N')) (mu : Fin d) (n : ℕ) :
    ∀ e ∈ (cmp99StraightPositivePath (G := SUN Nc) x mu n).edges,
      e.sign = true := by
  induction n with
  | zero => simp
  | succ n ih =>
      intro e he
      simp only [cmp99StraightPositivePath,
        OrientedLatticePath.castEnd_edges, OrientedLatticePath.trans,
        positiveCoordinatePath, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact ih e he
      · rfl

/-- The middle source contour `[x,x']` is a positive contour, with no
orientation hypothesis left for downstream consumers. -/
theorem cmp99SourceUbarGamma2_edges_pos
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    ∀ e ∈ cmp99SourceUbarGamma2 (G := SUN Nc) b x, e.sign = true := by
  exact cmp99StraightPositivePath_edges_pos (Nc := Nc) x b.2 M

/-- The literal entrance holonomy from the coarse basepoint to `x`. -/
def cmp98Gamma1PrefixHolonomy
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) : SUN Nc :=
  wilsonLine U (cmp99SourceUbarGamma1 (G := SUN Nc) b x)

/-- Source-shaped specialization of the ordered-path bridge to the middle
contour of CMP98 (124).  Its coordinate sum starts at the literal entrance
holonomy used in the transported line average of CMP98 (125). -/
theorem cmp98Gamma2_prefixCoordinateSum_eq_rightTrivializedVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    cmp98LieCoordMatrix
        (cmp98PositiveContourPrefixCoordinateSum U A
          (cmp98Gamma1PrefixHolonomy U b x)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b x)) =
      (cmp98Gamma1PrefixHolonomy U b x).val *
        (cmp98ContourFirstVariation U A
            (cmp99SourceUbarGamma2 (G := SUN Nc) b x) 0 *
          (cmp98ContourMatrixCurve U A
            (cmp99SourceUbarGamma2 (G := SUN Nc) b x) 0)ᴴ) *
        (cmp98Gamma1PrefixHolonomy U b x).valᴴ := by
  rw [cmp98LieCoordMatrix_prefixCoordinateSum U A
    (cmp98Gamma1PrefixHolonomy U b x)
    (cmp99SourceUbarGamma2 (G := SUN Nc) b x)
    (cmp99SourceUbarGamma2_edges_pos (Nc := Nc) b x)]
  rw [cmp98ContourFirstVariation_mul_conjTranspose_eq_rightVariation U A
    (cmp99SourceUbarGamma2 (G := SUN Nc) b x)
    (cmp99SourceUbarGamma2_edges_pos (Nc := Nc) b x)]

end

end YangMills.RG
