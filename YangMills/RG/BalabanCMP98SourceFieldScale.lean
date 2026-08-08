/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98UbarLogAverageFDeriv
import YangMills.RG.BalabanCMP116WilsonPlaquetteEnergy

/-!
# The source sup norm and contour-length budget in CMP98 (123)

The norm `|A|` in the printed estimate (123) is uniform over physical
bonds.  The repository's ambient cochain type carries an `L2` norm, so this
file records the finite source sup norm explicitly and proves that it
controls every oriented matrix generator without a volume factor.

It also packages the four literal contours entering (121) and proves their
total length is at most `2 * (d + 1) * M`.  These are the two source-specific
inputs from which the `M^2 * |A|^2` Taylor budget must be derived.  No
quadratic remainder estimate is assumed here.
-/

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The finite, volume-uniform field norm printed as `|A|` in CMP98. -/
def cmp98SourceFieldSupNorm
    (A : PhysicalGaugeOneCochain d (M * N') Nc) : ℝ :=
  (Finset.univ.image fun b : PhysicalBond d (M * N') => ‖A b‖).max'
    (by simp)

/-- Every physical bond coordinate is bounded by the source sup norm. -/
theorem norm_apply_le_cmp98SourceFieldSupNorm
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d (M * N')) :
    ‖A b‖ ≤ cmp98SourceFieldSupNorm A := by
  unfold cmp98SourceFieldSupNorm
  exact Finset.le_max' _ _ (by simp)

/-- The source sup norm is nonnegative. -/
theorem cmp98SourceFieldSupNorm_nonneg
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    0 ≤ cmp98SourceFieldSupNorm A :=
  (norm_nonneg (A (Classical.choice inferInstance))).trans
    (norm_apply_le_cmp98SourceFieldSupNorm A _)

/-- Every oriented `su(N)` generator occurring in a contour is controlled
by the same source sup norm, with no dependence on the ambient volume. -/
theorem norm_orientedWilsonGenerator_le_cmp98SourceFieldSupNorm
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) :
    ‖orientedWilsonGenerator A e‖ ≤ cmp98SourceFieldSupNorm A :=
  (norm_orientedWilsonGenerator_le_coordinate A e).trans
    (norm_apply_le_cmp98SourceFieldSupNorm A (physicalBondOfEdge e))

/-- The four literal edge lists in the local deviation of CMP98 (121).
The final list is the coarse path whose holonomy is conjugate-transposed in
the matrix formula; its length is unchanged by inversion. -/
def cmp98SourceFourContourEdges
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    List (ConcreteEdge d (M * N')) :=
  cmp99SourceUbarGamma1 (G := SUN Nc) b x ++
    cmp99SourceUbarGamma2 (G := SUN Nc) b x ++
    cmp99SourceUbarGamma3 (G := SUN Nc) b x ++
    reverseLatticePath (d := d) (N := M * N') (G := SUN Nc)
      (cmp98SourceCoarseBondPath (Nc := Nc) b)

/-- Exact decomposition of the four-contour length. -/
theorem cmp98SourceFourContourEdges_length
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    (cmp98SourceFourContourEdges (Nc := Nc) b x).length =
      (cmp99SourceUbarGamma1 (G := SUN Nc) b x).length +
      (cmp99SourceUbarGamma2 (G := SUN Nc) b x).length +
      (cmp99SourceUbarGamma3 (G := SUN Nc) b x).length +
      (cmp98SourceCoarseBondPath (Nc := Nc) (M := M) b).length := by
  simp [cmp98SourceFourContourEdges, reverseLatticePath, add_assoc]

/-- The straight coarse path has exactly `M` fine edges. -/
theorem cmp98SourceCoarseBondPath_length (b : PhysicalBond d N') :
    (cmp98SourceCoarseBondPath (Nc := Nc) (M := M) b).length = M := by
  exact cmp99SourceParallelTransportPath_length
    (G := SUN Nc) (blockBasepoint M N' b.1) b.2

/-- Uniform source budget for the complete four-contour word.  In the
physical range `x ∈ blockOf M N' b.1`, its length is linear in the block
scale and independent of the periodic volume. -/
theorem cmp98SourceFourContourEdges_length_le
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) :
    (cmp98SourceFourContourEdges (Nc := Nc) b x).length ≤
      2 * (d + 1) * M := by
  rw [cmp98SourceFourContourEdges_length,
    cmp99SourceUbarGamma2_length (G := SUN Nc),
    cmp98SourceCoarseBondPath_length (Nc := Nc)]
  have h1 := cmp99SourceUbarGamma1_length_le
    (G := SUN Nc) b x hx
  have h3 := cmp99SourceUbarGamma3_length_le
    (G := SUN Nc) b x hx
  have hscale : d * (M - 1) ≤ d * M :=
    Nat.mul_le_mul_left d (Nat.sub_le M 1)
  calc
    (cmp99SourceUbarGamma1 (G := SUN Nc) b x).length + M +
          (cmp99SourceUbarGamma3 (G := SUN Nc) b x).length + M
        ≤ d * (M - 1) + M + d * (M - 1) + M := by omega
    _ ≤ d * M + M + d * M + M := by omega
    _ = 2 * (d + 1) * M := by ring

/-- Every generator appearing in the literal four-contour word is bounded
by the same source field scale. -/
theorem norm_generator_of_mem_cmp98SourceFourContourEdges_le
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (e : ConcreteEdge d (M * N'))
    (_he : e ∈ cmp98SourceFourContourEdges (Nc := Nc) b x) :
    ‖orientedWilsonGenerator A e‖ ≤ cmp98SourceFieldSupNorm A :=
  norm_orientedWilsonGenerator_le_cmp98SourceFieldSupNorm A e

end

end YangMills.RG
