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

open YangMills Matrix

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

end

end YangMills.RG
