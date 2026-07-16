import YangMills.RG.BalabanCMP116FourFactorSecondDerivative

/-!
# Telescoping bounds for ordered four-factor matrix products

The arbitrary-background plaquette formula reduces its quantitative estimate
to finite products of four matrices.  This module proves the exact
noncommutative telescoping identity and a uniform operator-norm bound.  It is
independent of the Wilson dictionary and introduces no physical estimate as a
hypothesis.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ}

/-- Ordered product of four fixed matrices. -/
def fourMatrixProduct
    (A : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((A 0 * A 1) * A 2) * A 3

/-- Exact telescoping identity, preserving the noncommutative factor order. -/
theorem fourMatrixProduct_sub_eq_telescoping
    (A B : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    fourMatrixProduct A - fourMatrixProduct B =
      (((A 0 - B 0) * A 1) * A 2) * A 3 +
      ((B 0 * (A 1 - B 1)) * A 2) * A 3 +
      ((B 0 * B 1) * (A 2 - B 2)) * A 3 +
      ((B 0 * B 1) * B 2) * (A 3 - B 3) := by
  simp only [fourMatrixProduct]
  noncomm_ring

/-- Operator norm of a product of four matrices. -/
theorem norm_fourMatrixProduct_le
    (A : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖fourMatrixProduct A‖ ≤
      ‖A 0‖ * ‖A 1‖ * ‖A 2‖ * ‖A 3‖ := by
  unfold fourMatrixProduct
  calc
    ‖((A 0 * A 1) * A 2) * A 3‖
        ≤ ‖(A 0 * A 1) * A 2‖ * ‖A 3‖ :=
          Matrix.l2_opNorm_mul _ _
    _ ≤ (‖A 0 * A 1‖ * ‖A 2‖) * ‖A 3‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ ((‖A 0‖ * ‖A 1‖) * ‖A 2‖) * ‖A 3‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _

set_option maxHeartbeats 800000 in

/-- A four-factor product is Lipschitz in its factors on a uniform norm ball.

The constant `4 * δ * L^3` is independent of the matrix dimension and of any
lattice volume.
-/
theorem norm_fourMatrixProduct_sub_le
    (A B : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ)
    (L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hA : ∀ i : Fin 4, ‖A i‖ ≤ L)
    (hB : ∀ i : Fin 4, ‖B i‖ ≤ L)
    (hdiff : ∀ i : Fin 4, ‖A i - B i‖ ≤ δ) :
    ‖fourMatrixProduct A - fourMatrixProduct B‖ ≤
      4 * δ * L ^ 3 := by
  rw [fourMatrixProduct_sub_eq_telescoping]
  let T0 := (((A 0 - B 0) * A 1) * A 2) * A 3
  let T1 := ((B 0 * (A 1 - B 1)) * A 2) * A 3
  let T2 := ((B 0 * B 1) * (A 2 - B 2)) * A 3
  let T3 := ((B 0 * B 1) * B 2) * (A 3 - B 3)
  have ht0 : ‖T0‖ ≤ δ * L ^ 3 := by
    calc
      ‖T0‖ ≤ ‖A 0 - B 0‖ * ‖A 1‖ * ‖A 2‖ * ‖A 3‖ :=
        norm_fourMatrixProduct_le
          (fun i => ![A 0 - B 0, A 1, A 2, A 3] i)
      _ ≤ δ * L * L * L := by
        gcongr
        · exact hdiff 0
        · exact hA 1
        · exact hA 2
        · exact hA 3
      _ = δ * L ^ 3 := by ring
  have ht1 : ‖T1‖ ≤ δ * L ^ 3 := by
    calc
      ‖T1‖ ≤ ‖B 0‖ * ‖A 1 - B 1‖ * ‖A 2‖ * ‖A 3‖ :=
        norm_fourMatrixProduct_le
          (fun i => ![B 0, A 1 - B 1, A 2, A 3] i)
      _ ≤ L * δ * L * L := by
        gcongr
        · exact hB 0
        · exact hdiff 1
        · exact hA 2
        · exact hA 3
      _ = δ * L ^ 3 := by ring
  have ht2 : ‖T2‖ ≤ δ * L ^ 3 := by
    calc
      ‖T2‖ ≤ ‖B 0‖ * ‖B 1‖ * ‖A 2 - B 2‖ * ‖A 3‖ :=
        norm_fourMatrixProduct_le
          (fun i => ![B 0, B 1, A 2 - B 2, A 3] i)
      _ ≤ L * L * δ * L := by
        gcongr
        · exact hB 0
        · exact hB 1
        · exact hdiff 2
        · exact hA 3
      _ = δ * L ^ 3 := by ring
  have ht3 : ‖T3‖ ≤ δ * L ^ 3 := by
    calc
      ‖T3‖ ≤ ‖B 0‖ * ‖B 1‖ * ‖B 2‖ * ‖A 3 - B 3‖ :=
        norm_fourMatrixProduct_le
          (fun i => ![B 0, B 1, B 2, A 3 - B 3] i)
      _ ≤ L * L * L * δ := by
        gcongr
        · exact hB 0
        · exact hB 1
        · exact hB 2
        · exact hdiff 3
      _ = δ * L ^ 3 := by ring
  calc
    ‖T0 + T1 + T2 + T3‖
        ≤ ‖T0 + T1 + T2‖ + ‖T3‖ := norm_add_le _ _
    _ ≤ (‖T0 + T1‖ + ‖T2‖) + ‖T3‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((‖T0‖ + ‖T1‖) + ‖T2‖) + ‖T3‖ := by
      gcongr
      exact norm_add_le _ _
    _ = ‖T0‖ + ‖T1‖ + ‖T2‖ + ‖T3‖ := by ring
    _ ≤ δ * L ^ 3 + δ * L ^ 3 + δ * L ^ 3 + δ * L ^ 3 := by
      gcongr
    _ = 4 * δ * L ^ 3 := by ring

end

end YangMills.RG
