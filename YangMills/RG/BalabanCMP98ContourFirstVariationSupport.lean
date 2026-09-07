/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98ContourFirstVariation
import YangMills.RG.BalabanCMP116WilsonOrientedEdgeMixedBounds

/-!
# Exact support of the first variation of a physical Wilson contour

The first variation of an ordered Wilson product is supported on the
positive bonds underlying its literal oriented edges.  This module proves
that statement at the recursive matrix level and transports it to the
ambient Fréchet derivative.

The final theorem is the form needed by the CMP109 pivot dictionary: a
single-bond probe has zero contour derivative whenever its physical bond is
absent from the contour.  No decay estimate or abstract support certificate
is used.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- An oriented generator vanishes when the underlying positive-bond
coordinate of the physical cochain vanishes. -/
theorem orientedWilsonGenerator_eq_zero_of_apply_eq_zero
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N'))
    (hA : A (physicalBondOfEdge e) = 0) :
    orientedWilsonGenerator A e = 0 := by
  unfold orientedWilsonGenerator flatOrientedSuMatrixTangent
  rw [hA]
  split <;> simp [SuLie.toMatrix] <;> rfl

/-- If every generator on a contour is zero, its ordered first variation is
exactly zero. -/
theorem cmp98ContourFirstVariation_zero_of_generators
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N')))
    (hzero : ∀ e ∈ es, orientedWilsonGenerator A e = 0) :
    cmp98ContourFirstVariation U A es 0 = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      have he : orientedWilsonGenerator A e = 0 :=
        hzero e (by simp)
      have hes : ∀ f ∈ es, orientedWilsonGenerator A f = 0 := by
        intro f hf
        exact hzero f (by simp [hf])
      simp only [cmp98ContourFirstVariation]
      rw [ih hes]
      simp only [mul_zero, add_zero]
      rw [orientedWilsonFactorFirst_zero_eq, he]
      split <;> simp

/-- A physical field vanishing on every positive bond underlying the
contour has zero ambient contour derivative. -/
theorem fderiv_cmp98AmbientWilsonLineMatrix_zero_apply_physical_of_support
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N')))
    (hzero : ∀ e ∈ es, A (physicalBondOfEdge e) = 0) :
    fderiv ℝ (fun Z => cmp98AmbientWilsonLineMatrix U Z es) 0
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) = 0 := by
  calc
    fderiv ℝ (fun Z => cmp98AmbientWilsonLineMatrix U Z es) 0
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) =
        cmp98ContourFirstVariation U A es 0 :=
      fderiv_cmp98AmbientWilsonLineMatrix_zero_apply_physical U A es
    _ = 0 := by
      apply cmp98ContourFirstVariation_zero_of_generators
      intro e he
      exact orientedWilsonGenerator_eq_zero_of_apply_eq_zero A e (hzero e he)

/-- A single physical-bond probe has zero contour derivative if the contour
does not contain that positive bond in either orientation. -/
theorem fderiv_cmp98AmbientWilsonLineMatrix_zero_apply_single_of_avoids
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (p : PhysicalBond d (M * N')) (v : SUNLieCoord Nc)
    (es : List (ConcreteEdge d (M * N')))
    (havoid : ∀ e ∈ es, physicalBondOfEdge e ≠ p) :
    fderiv ℝ (fun Z => cmp98AmbientWilsonLineMatrix U Z es) 0
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent
            (singlePhysicalBondCochain p v))) = 0 := by
  apply fderiv_cmp98AmbientWilsonLineMatrix_zero_apply_physical_of_support
  intro e he
  exact singlePhysicalBondCochain_of_ne v (havoid e he)

end

end YangMills.RG
