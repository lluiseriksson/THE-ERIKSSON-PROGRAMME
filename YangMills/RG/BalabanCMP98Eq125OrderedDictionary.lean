/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98OrderedContourTransport
import YangMills.RG.BalabanCMP98Eq125MainLinearAverage

/-!
# Ordered-contour dictionary for CMP98 (125)

This module identifies the recursive prefix transport obtained by
differentiating the literal middle contour with the finite transported line
sum printed in CMP98 (125).  The result is an exact dictionary theorem; it
does not identify the three remaining correction terms of CMP98 (124).
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped BigOperators

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The literal `k`-th positive edge of the straight source contour. -/
def cmp98StraightPositiveEdge
    (x : FinBox d (M * N')) (mu : Fin d) (k : ℕ) :
    ConcreteEdge d (M * N') :=
  ⟨(fun y => FinBox.shift y mu)^[k] x, mu, true⟩

/-- Exact ordered edge list of the straight source contour. -/
theorem cmp99StraightPositivePath_edges_eq_range_map
    (x : FinBox d (M * N')) (mu : Fin d) (n : ℕ) :
    (cmp99StraightPositivePath (G := SUN Nc) x mu n).edges =
      (List.range n).map (cmp98StraightPositiveEdge x mu) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [cmp99StraightPositivePath,
        OrientedLatticePath.castEnd_edges, OrientedLatticePath.trans,
        positiveCoordinatePath, ih, List.range_succ, List.map_append,
        List.map_singleton]
      rfl

/-- Prefix transport distributes over concatenation, with the second list
starting at the holonomy accumulated along the first. -/
theorem cmp98PositiveContourPrefixCoordinateSum_append
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (pfx : SUN Nc) (es fs : List (ConcreteEdge d (M * N')))
    (hpos : ∀ e ∈ es, e.sign = true) :
    cmp98PositiveContourPrefixCoordinateSum U A pfx (es ++ fs) =
      cmp98PositiveContourPrefixCoordinateSum U A pfx es +
        cmp98PositiveContourPrefixCoordinateSum U A
          (pfx * wilsonLine U es) fs := by
  induction es generalizing pfx with
  | nil =>
      simp only [List.nil_append,
        cmp98PositiveContourPrefixCoordinateSum]
      rw [wilsonLine_nil, mul_one]
      simp
  | cons e es ih =>
      have he : e.sign = true := hpos e (by simp)
      have hes : ∀ f ∈ es, f.sign = true := by
        intro f hf
        exact hpos f (by simp [hf])
      simp only [List.cons_append,
        cmp98PositiveContourPrefixCoordinateSum]
      rw [ih _ hes]
      rw [wilsonLine_cons]
      simp only [cmp98PositiveBaseSUN]
      have hedge :
          e = positiveEdgeOfPhysicalBond (physicalBondOfEdge e) := by
        rcases e with ⟨source, dir, sign⟩
        cases sign <;>
          simp_all [physicalBondOfEdge, positiveEdgeOfPhysicalBond]
      rw [hedge]
      simp only [mul_assoc]
      abel

/-- The first `k` edges of the length-`n` straight contour are exactly the
length-`k` straight contour. -/
theorem cmp99StraightPositivePath_take_edges
    (x : FinBox d (M * N')) (mu : Fin d) {k n : ℕ} (hkn : k ≤ n) :
    (cmp99StraightPositivePath (G := SUN Nc) x mu n).edges.take k =
      (cmp99StraightPositivePath (G := SUN Nc) x mu k).edges := by
  rw [cmp99StraightPositivePath_edges_eq_range_map,
    cmp99StraightPositivePath_edges_eq_range_map, ← List.map_take]
  simp [List.take_range, Nat.min_eq_left hkn]

/-- Adding the last edge of a straight contour adds its generator transported
by the holonomy of the preceding prefix. -/
theorem cmp98PositiveContourPrefixCoordinateSum_straight_succ
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (pfx : SUN Nc) (x : FinBox d (M * N')) (mu : Fin d) (n : ℕ) :
    cmp98PositiveContourPrefixCoordinateSum U A pfx
        (cmp99StraightPositivePath (G := SUN Nc) x mu (n + 1)).edges =
      cmp98PositiveContourPrefixCoordinateSum U A pfx
          (cmp99StraightPositivePath (G := SUN Nc) x mu n).edges +
        (matrixSUNAdjointModel Nc).adCLM
          (pfx * wilsonLine U
            (cmp99StraightPositivePath (G := SUN Nc) x mu n).edges)
          (A (((fun y => FinBox.shift y mu)^[n] x), mu)) := by
  simp only [cmp99StraightPositivePath,
    OrientedLatticePath.castEnd_edges, OrientedLatticePath.trans,
    positiveCoordinatePath]
  rw [cmp98PositiveContourPrefixCoordinateSum_append]
  · simp [cmp98PositiveContourPrefixCoordinateSum,
      cmp98PositiveBaseSUN, cmp98StraightPositiveEdge,
      physicalBondOfEdge]
  · exact cmp99StraightPositivePath_edges_pos (Nc := Nc) x mu n

/-- Closed finite-sum form of the recursively transported straight contour. -/
theorem cmp98PositiveContourPrefixCoordinateSum_straight
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (pfx : SUN Nc) (x : FinBox d (M * N')) (mu : Fin d) (n : ℕ) :
    cmp98PositiveContourPrefixCoordinateSum U A pfx
        (cmp99StraightPositivePath (G := SUN Nc) x mu n).edges =
      ∑ k ∈ Finset.range n,
        (matrixSUNAdjointModel Nc).adCLM
          (pfx * wilsonLine U
            (cmp99StraightPositivePath (G := SUN Nc) x mu k).edges)
          (A (((fun y => FinBox.shift y mu)^[k] x), mu)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [cmp98PositiveContourPrefixCoordinateSum_straight_succ, ih,
        Finset.sum_range_succ]

/-- The entrance prefix used by the ordered variation is definitionally the
block-contour holonomy used in CMP98 (125). -/
theorem cmp98Gamma1PrefixHolonomy_eq_cmp99ContourHolonomy
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' b.1}) :
    cmp98Gamma1PrefixHolonomy U b x.1 =
      cmp99ContourHolonomy
        (cmp99BlockContainedContourSystem (G := SUN Nc)) U b.1 x.1 := by
  rfl

/-- The prefix holonomy in CMP98 (125) is the entrance holonomy followed by
the literal first `k` middle-contour edges. -/
theorem cmp98Eq125PrefixHolonomy_eq_gamma1_mul_straight
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' b.1})
    {k : ℕ} (hk : k ≤ M) :
    cmp98Eq125PrefixHolonomy U b.1 x b.2 k =
      cmp98Gamma1PrefixHolonomy U b x.1 *
        wilsonLine U
          (cmp99StraightPositivePath (G := SUN Nc) x.1 b.2 k).edges := by
  rw [cmp98Eq125PrefixHolonomy,
    cmp98Gamma1PrefixHolonomy_eq_cmp99ContourHolonomy]
  unfold cmp99SourceParallelTransportPath
  rw [cmp99StraightPositivePath_take_edges (Nc := Nc) x.1 b.2 hk]

/-- Exact source dictionary: the recursively transported middle-contour
variation is the finite transported line sum printed in CMP98 (125). -/
theorem cmp98Gamma2_prefixCoordinateSum_eq_eq125TransportedLineSum
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' b.1}) :
    cmp98PositiveContourPrefixCoordinateSum U A
        (cmp98Gamma1PrefixHolonomy U b x.1)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b x.1) =
      cmp98Eq125TransportedLineSum (matrixSUNAdjointModel Nc)
        U A b.1 x b.2 := by
  rw [cmp99SourceUbarGamma2,
    cmp99SourceParallelTransportPath,
    cmp98PositiveContourPrefixCoordinateSum_straight]
  unfold cmp98Eq125TransportedLineSum
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [cmp98Eq125TransportedEdgeValue,
    cmp98Eq125PrefixHolonomy_eq_gamma1_mul_straight
      (Nc := Nc) U b x (Nat.le_of_lt hk)]

/-- Matrix-level terminal dictionary between the printed line sum and the
right-trivialized derivative of the literal middle contour. -/
theorem cmp98LieCoordMatrix_eq125TransportedLineSum_eq_rightVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' b.1}) :
    cmp98LieCoordMatrix
        (cmp98Eq125TransportedLineSum (matrixSUNAdjointModel Nc)
          U A b.1 x b.2) =
      (cmp98Gamma1PrefixHolonomy U b x.1).val *
        (cmp98ContourFirstVariation U A
            (cmp99SourceUbarGamma2 (G := SUN Nc) b x.1) 0 *
          (cmp98ContourMatrixCurve U A
            (cmp99SourceUbarGamma2 (G := SUN Nc) b x.1) 0)ᴴ) *
        (cmp98Gamma1PrefixHolonomy U b x.1).valᴴ := by
  rw [← cmp98Gamma2_prefixCoordinateSum_eq_eq125TransportedLineSum U A b x]
  exact cmp98Gamma2_prefixCoordinateSum_eq_rightTrivializedVariation
    U A b x.1

/-- The coordinate/matrix dictionary also preserves real scaling. -/
theorem cmp98LieCoordMatrix_smul (r : ℝ) (X : SUNLieCoord Nc) :
    cmp98LieCoordMatrix (r • X) = r • cmp98LieCoordMatrix X := by
  simp only [cmp98LieCoordMatrix, map_smul]
  rfl

/-- The coordinate/matrix dictionary preserves finite sums. -/
theorem cmp98LieCoordMatrix_sum
    {ι : Type*} (s : Finset ι) (X : ι → SUNLieCoord Nc) :
    cmp98LieCoordMatrix (∑ i ∈ s, X i) =
      ∑ i ∈ s, cmp98LieCoordMatrix (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cmp98LieCoordMatrix_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        cmp98LieCoordMatrix_add, ih]

/-- Exact block-averaged matrix form of the main term (125). -/
theorem cmp98LieCoordMatrix_eq125MainAverageValue
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98LieCoordMatrix
        (cmp98Eq125MainAverageValue (matrixSUNAdjointModel Nc) U A b) =
      cmp98Eq125MainAverageWeight M d •
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' b.1},
          (cmp98Gamma1PrefixHolonomy U b x.1).val *
            (cmp98ContourFirstVariation U A
                (cmp99SourceUbarGamma2 (G := SUN Nc) b x.1) 0 *
              (cmp98ContourMatrixCurve U A
                (cmp99SourceUbarGamma2 (G := SUN Nc) b x.1) 0)ᴴ) *
            (cmp98Gamma1PrefixHolonomy U b x.1).valᴴ := by
  rw [cmp98Eq125MainAverageValue, cmp98LieCoordMatrix_smul]
  simp_rw [cmp98LieCoordMatrix_sum,
    cmp98LieCoordMatrix_eq125TransportedLineSum_eq_rightVariation]

/-- The source normalization of (125) is exactly one inverse block length
times the `M⁻ᵈ` normalization of the logarithmic block average in (124). -/
theorem cmp98LieCoordMatrix_eq125MainAverageValue_normalized
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98LieCoordMatrix
        (cmp98Eq125MainAverageValue (matrixSUNAdjointModel Nc) U A b) =
      (M : ℝ)⁻¹ •
        (((M : ℝ) ^ d)⁻¹ •
          ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' b.1},
            (cmp98Gamma1PrefixHolonomy U b x.1).val *
              (cmp98ContourFirstVariation U A
                  (cmp99SourceUbarGamma2 (G := SUN Nc) b x.1) 0 *
                (cmp98ContourMatrixCurve U A
                  (cmp99SourceUbarGamma2 (G := SUN Nc) b x.1) 0)ᴴ) *
              (cmp98Gamma1PrefixHolonomy U b x.1).valᴴ) := by
  rw [cmp98LieCoordMatrix_eq125MainAverageValue,
    cmp98Eq125MainAverageWeight_eq_inv_mul_flatWeight]
  rw [smul_smul]

end

end YangMills.RG
