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

/-- Heterogeneous telescoping bound for four ordered factors.

Each position keeps its own norm.  In particular, if a generator factor is
identical in `A` and `B`, its difference term vanishes instead of being
absorbed into a common radius.
-/
theorem norm_fourMatrixProduct_sub_le_heterogeneous
    (A B : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖fourMatrixProduct A - fourMatrixProduct B‖ ≤
      ‖A 0 - B 0‖ * ‖A 1‖ * ‖A 2‖ * ‖A 3‖ +
      ‖B 0‖ * ‖A 1 - B 1‖ * ‖A 2‖ * ‖A 3‖ +
      ‖B 0‖ * ‖B 1‖ * ‖A 2 - B 2‖ * ‖A 3‖ +
      ‖B 0‖ * ‖B 1‖ * ‖B 2‖ * ‖A 3 - B 3‖ := by
  rw [fourMatrixProduct_sub_eq_telescoping]
  calc
    ‖(((A 0 - B 0) * A 1) * A 2) * A 3 +
        ((B 0 * (A 1 - B 1)) * A 2) * A 3 +
        ((B 0 * B 1) * (A 2 - B 2)) * A 3 +
        ((B 0 * B 1) * B 2) * (A 3 - B 3)‖
        ≤ ‖(((A 0 - B 0) * A 1) * A 2) * A 3‖ +
            ‖((B 0 * (A 1 - B 1)) * A 2) * A 3‖ +
            ‖((B 0 * B 1) * (A 2 - B 2)) * A 3‖ +
            ‖((B 0 * B 1) * B 2) * (A 3 - B 3)‖ := by
          calc
            ‖(((A 0 - B 0) * A 1) * A 2) * A 3 +
                ((B 0 * (A 1 - B 1)) * A 2) * A 3 +
                ((B 0 * B 1) * (A 2 - B 2)) * A 3 +
                ((B 0 * B 1) * B 2) * (A 3 - B 3)‖
                ≤ ‖(((A 0 - B 0) * A 1) * A 2) * A 3 +
                    ((B 0 * (A 1 - B 1)) * A 2) * A 3 +
                    ((B 0 * B 1) * (A 2 - B 2)) * A 3‖ +
                  ‖((B 0 * B 1) * B 2) * (A 3 - B 3)‖ :=
                    norm_add_le _ _
            _ ≤ (‖(((A 0 - B 0) * A 1) * A 2) * A 3 +
                    ((B 0 * (A 1 - B 1)) * A 2) * A 3‖ +
                  ‖((B 0 * B 1) * (A 2 - B 2)) * A 3‖) +
                  ‖((B 0 * B 1) * B 2) * (A 3 - B 3)‖ := by
                    gcongr
                    exact norm_add_le _ _
            _ ≤ ((‖(((A 0 - B 0) * A 1) * A 2) * A 3‖ +
                    ‖((B 0 * (A 1 - B 1)) * A 2) * A 3‖) +
                  ‖((B 0 * B 1) * (A 2 - B 2)) * A 3‖) +
                  ‖((B 0 * B 1) * B 2) * (A 3 - B 3)‖ := by
                    gcongr
                    exact norm_add_le _ _
            _ = _ := by ring
    _ ≤
        (‖A 0 - B 0‖ * ‖A 1‖ * ‖A 2‖ * ‖A 3‖) +
        (‖B 0‖ * ‖A 1 - B 1‖ * ‖A 2‖ * ‖A 3‖) +
        (‖B 0‖ * ‖B 1‖ * ‖A 2 - B 2‖ * ‖A 3‖) +
        (‖B 0‖ * ‖B 1‖ * ‖B 2‖ * ‖A 3 - B 3‖) := by
      gcongr
      · exact norm_fourMatrixProduct_le
          (fun i => ![A 0 - B 0, A 1, A 2, A 3] i)
      · exact norm_fourMatrixProduct_le
          (fun i => ![B 0, A 1 - B 1, A 2, A 3] i)
      · exact norm_fourMatrixProduct_le
          (fun i => ![B 0, B 1, A 2 - B 2, A 3] i)
      · exact norm_fourMatrixProduct_le
          (fun i => ![B 0, B 1, B 2, A 3 - B 3] i)

/-- If only the two background slots vary, the heterogeneous bound preserves
the two generator norms exactly. -/
theorem norm_fourMatrixProduct_sub_le_two_fixed_generators
    (W W' : Fin 2 → Matrix (Fin Nc) (Fin Nc) ℂ)
    (X Y : Matrix (Fin Nc) (Fin Nc) ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hW : ∀ i : Fin 2, ‖W i‖ ≤ 1)
    (hW' : ∀ i : Fin 2, ‖W' i‖ ≤ 1)
    (hdiff : ∀ i : Fin 2, ‖W i - W' i‖ ≤ δ) :
    ‖fourMatrixProduct ![W 0, X, Y, W 1] -
        fourMatrixProduct ![W' 0, X, Y, W' 1]‖ ≤
      2 * δ * ‖X‖ * ‖Y‖ := by
  have htel :
      fourMatrixProduct ![W 0, X, Y, W 1] -
          fourMatrixProduct ![W' 0, X, Y, W' 1] =
        (((W 0 - W' 0) * X) * Y) * W 1 +
        ((W' 0 * X) * Y) * (W 1 - W' 1) := by
    simp only [fourMatrixProduct]
    noncomm_ring
  rw [htel]
  calc
    ‖(((W 0 - W' 0) * X) * Y) * W 1 +
        ((W' 0 * X) * Y) * (W 1 - W' 1)‖
        ≤ ‖(((W 0 - W' 0) * X) * Y) * W 1‖ +
          ‖((W' 0 * X) * Y) * (W 1 - W' 1)‖ := norm_add_le _ _
    _ ≤ ‖W 0 - W' 0‖ * ‖X‖ * ‖Y‖ * ‖W 1‖ +
          ‖W' 0‖ * ‖X‖ * ‖Y‖ * ‖W 1 - W' 1‖ := by
      gcongr
      · exact norm_fourMatrixProduct_le
          (fun i => ![W 0 - W' 0, X, Y, W 1] i)
      · exact norm_fourMatrixProduct_le
          (fun i => ![W' 0, X, Y, W 1 - W' 1] i)
    _ ≤ δ * ‖X‖ * ‖Y‖ * 1 +
          1 * ‖X‖ * ‖Y‖ * δ := by
      gcongr
      · exact hdiff 0
      · exact hW 1
      · exact hW' 0
      · exact hdiff 1
    _ = 2 * δ * ‖X‖ * ‖Y‖ := by ring

/-- Relative heterogeneous bound with one scale assigned to each factor.

This is the form used for mixed Hessian monomials.  Background slots take
scale `1`; the two differentiated slots take their respective generator
norms.  Thus the right-hand side remains bilinear in those generators.
-/
theorem norm_fourMatrixProduct_sub_le_scaled
    (A B : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ)
    (g : Fin 4 → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hg : ∀ i, 0 ≤ g i)
    (hA : ∀ i, ‖A i‖ ≤ g i)
    (hB : ∀ i, ‖B i‖ ≤ g i)
    (hdiff : ∀ i, ‖A i - B i‖ ≤ ε * g i) :
    ‖fourMatrixProduct A - fourMatrixProduct B‖ ≤
      4 * ε * (g 0 * g 1 * g 2 * g 3) := by
  have h0 :
      ‖A 0 - B 0‖ * ‖A 1‖ * ‖A 2‖ * ‖A 3‖ ≤
        (ε * g 0) * g 1 * g 2 * g 3 := by
    calc
      ‖A 0 - B 0‖ * ‖A 1‖ * ‖A 2‖ * ‖A 3‖
          ≤ (ε * g 0) * ‖A 1‖ * ‖A 2‖ * ‖A 3‖ := by
            gcongr
            exact hdiff 0
      _ ≤ (ε * g 0) * g 1 * ‖A 2‖ * ‖A 3‖ := by
            gcongr
            exact mul_nonneg hε (hg 0)
            exact hA 1
      _ ≤ (ε * g 0) * g 1 * g 2 * ‖A 3‖ := by
            gcongr
            · exact mul_nonneg (mul_nonneg hε (hg 0)) (hg 1)
            · exact hA 2
      _ ≤ (ε * g 0) * g 1 * g 2 * g 3 := by
            gcongr
            · exact mul_nonneg
                (mul_nonneg (mul_nonneg hε (hg 0)) (hg 1)) (hg 2)
            · exact hA 3
  have h1 :
      ‖B 0‖ * ‖A 1 - B 1‖ * ‖A 2‖ * ‖A 3‖ ≤
        g 0 * (ε * g 1) * g 2 * g 3 := by
    calc
      ‖B 0‖ * ‖A 1 - B 1‖ * ‖A 2‖ * ‖A 3‖
          ≤ g 0 * ‖A 1 - B 1‖ * ‖A 2‖ * ‖A 3‖ := by
            gcongr
            exact hB 0
      _ ≤ g 0 * (ε * g 1) * ‖A 2‖ * ‖A 3‖ := by
            gcongr
            · exact hg 0
            · exact hdiff 1
      _ ≤ g 0 * (ε * g 1) * g 2 * ‖A 3‖ := by
            gcongr
            · exact mul_nonneg (hg 0) (mul_nonneg hε (hg 1))
            · exact hA 2
      _ ≤ g 0 * (ε * g 1) * g 2 * g 3 := by
            gcongr
            · exact mul_nonneg
                (mul_nonneg (hg 0) (mul_nonneg hε (hg 1))) (hg 2)
            · exact hA 3
  have h2 :
      ‖B 0‖ * ‖B 1‖ * ‖A 2 - B 2‖ * ‖A 3‖ ≤
        g 0 * g 1 * (ε * g 2) * g 3 := by
    calc
      ‖B 0‖ * ‖B 1‖ * ‖A 2 - B 2‖ * ‖A 3‖
          ≤ g 0 * ‖B 1‖ * ‖A 2 - B 2‖ * ‖A 3‖ := by
            gcongr
            exact hB 0
      _ ≤ g 0 * g 1 * ‖A 2 - B 2‖ * ‖A 3‖ := by
            gcongr
            · exact hg 0
            · exact hB 1
      _ ≤ g 0 * g 1 * (ε * g 2) * ‖A 3‖ := by
            gcongr
            · exact mul_nonneg (hg 0) (hg 1)
            · exact hdiff 2
      _ ≤ g 0 * g 1 * (ε * g 2) * g 3 := by
            gcongr
            · exact mul_nonneg
                (mul_nonneg (hg 0) (hg 1)) (mul_nonneg hε (hg 2))
            · exact hA 3
  have h3 :
      ‖B 0‖ * ‖B 1‖ * ‖B 2‖ * ‖A 3 - B 3‖ ≤
        g 0 * g 1 * g 2 * (ε * g 3) := by
    calc
      ‖B 0‖ * ‖B 1‖ * ‖B 2‖ * ‖A 3 - B 3‖
          ≤ g 0 * ‖B 1‖ * ‖B 2‖ * ‖A 3 - B 3‖ := by
            gcongr
            exact hB 0
      _ ≤ g 0 * g 1 * ‖B 2‖ * ‖A 3 - B 3‖ := by
            gcongr
            · exact hg 0
            · exact hB 1
      _ ≤ g 0 * g 1 * g 2 * ‖A 3 - B 3‖ := by
            gcongr
            · exact mul_nonneg (hg 0) (hg 1)
            · exact hB 2
      _ ≤ g 0 * g 1 * g 2 * (ε * g 3) := by
            gcongr
            · exact mul_nonneg (mul_nonneg (hg 0) (hg 1)) (hg 2)
            · exact hdiff 3
  calc
    ‖fourMatrixProduct A - fourMatrixProduct B‖
        ≤ ‖A 0 - B 0‖ * ‖A 1‖ * ‖A 2‖ * ‖A 3‖ +
          ‖B 0‖ * ‖A 1 - B 1‖ * ‖A 2‖ * ‖A 3‖ +
          ‖B 0‖ * ‖B 1‖ * ‖A 2 - B 2‖ * ‖A 3‖ +
          ‖B 0‖ * ‖B 1‖ * ‖B 2‖ * ‖A 3 - B 3‖ :=
      norm_fourMatrixProduct_sub_le_heterogeneous A B
    _ ≤ (ε * g 0) * g 1 * g 2 * g 3 +
          g 0 * (ε * g 1) * g 2 * g 3 +
          g 0 * g 1 * (ε * g 2) * g 3 +
          g 0 * g 1 * g 2 * (ε * g 3) := by
      exact add_le_add (add_le_add (add_le_add h0 h1) h2) h3
    _ = 4 * ε * (g 0 * g 1 * g 2 * g 3) := by ring

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
