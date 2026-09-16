import YangMills.RG.BalabanCMP116FourFactorMixed

/-!
# Bilinear Lipschitz bound for the mixed four-factor formula

The direct mixed variation contains sixteen ordered monomials.  Background
factors have scale `1`, first variations have scales `LA` and `LB`, and mixed
single-factor variations have scale `LA * LB`.  Applying the heterogeneous
four-product estimate to every monomial preserves bilinearity:

`‖mixed(U) - mixed(V)‖ ≤ 64 * ε * LA * LB`.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- The sixteen ordered monomials in the direct mixed four-factor formula. -/
def fourFactorMixedFactors
    (W XA XB YAB : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    Fin 16 → Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ :=
  ![
    ![YAB 0, W 1, W 2, W 3],
    ![XA 0, XB 1, W 2, W 3],
    ![XB 0, XA 1, W 2, W 3],
    ![XA 0, W 1, XB 2, W 3],
    ![XB 0, W 1, XA 2, W 3],
    ![XA 0, W 1, W 2, XB 3],
    ![XB 0, W 1, W 2, XA 3],
    ![W 0, YAB 1, W 2, W 3],
    ![W 0, XA 1, XB 2, W 3],
    ![W 0, XB 1, XA 2, W 3],
    ![W 0, XA 1, W 2, XB 3],
    ![W 0, XB 1, W 2, XA 3],
    ![W 0, W 1, YAB 2, W 3],
    ![W 0, W 1, XA 2, XB 3],
    ![W 0, W 1, XB 2, XA 3],
    ![W 0, W 1, W 2, YAB 3]
  ]

/-- The expanded sixteen-term sum is the original mixed formula. -/
theorem fourFactorMixed_eq_sum_products
    (W XA XB YAB : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    fourFactorMixed W XA XB YAB =
      ∑ i : Fin 16,
        fourMatrixProduct (fourFactorMixedFactors W XA XB YAB i) := by
  simp [fourFactorMixed, fourFactorMixedFactors, fourMatrixProduct,
    Fin.sum_univ_succ]
  noncomm_ring

/-- Four explicit relative factor scales, avoiding a common-radius loss. -/
theorem norm_fourMatrixProduct_sub_le_four_scales
    (A B : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ)
    (s0 s1 s2 s3 ε : ℝ)
    (hε : 0 ≤ ε) (h0 : 0 ≤ s0) (h1 : 0 ≤ s1)
    (h2 : 0 ≤ s2) (h3 : 0 ≤ s3)
    (hA0 : ‖A 0‖ ≤ s0) (hA1 : ‖A 1‖ ≤ s1)
    (hA2 : ‖A 2‖ ≤ s2) (hA3 : ‖A 3‖ ≤ s3)
    (hB0 : ‖B 0‖ ≤ s0) (hB1 : ‖B 1‖ ≤ s1)
    (hB2 : ‖B 2‖ ≤ s2) (hB3 : ‖B 3‖ ≤ s3)
    (hd0 : ‖A 0 - B 0‖ ≤ ε * s0)
    (hd1 : ‖A 1 - B 1‖ ≤ ε * s1)
    (hd2 : ‖A 2 - B 2‖ ≤ ε * s2)
    (hd3 : ‖A 3 - B 3‖ ≤ ε * s3) :
    ‖fourMatrixProduct A - fourMatrixProduct B‖ ≤
      4 * ε * (s0 * s1 * s2 * s3) := by
  apply norm_fourMatrixProduct_sub_le_scaled A B ![s0, s1, s2, s3] ε hε
  · intro i
    fin_cases i <;> simp [h0, h1, h2, h3]
  · intro i
    fin_cases i
    · exact hA0
    · exact hA1
    · exact hA2
    · exact hA3
  · intro i
    fin_cases i
    · exact hB0
    · exact hB1
    · exact hB2
    · exact hB3
  · intro i
    fin_cases i
    · exact hd0
    · exact hd1
    · exact hd2
    · exact hd3

set_option maxHeartbeats 1600000 in
/-- Dimension- and volume-independent bilinear Lipschitz estimate for the
direct mixed four-factor formula. -/
theorem norm_fourFactorMixed_sub_le
    (W W' XA XA' XB XB' YAB YAB' :
      Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ)
    (LA LB ε : ℝ)
    (hLA : 0 ≤ LA) (hLB : 0 ≤ LB) (hε : 0 ≤ ε)
    (hW : ∀ i, ‖W i‖ ≤ 1)
    (hW' : ∀ i, ‖W' i‖ ≤ 1)
    (hWdiff : ∀ i, ‖W i - W' i‖ ≤ ε)
    (hXA : ∀ i, ‖XA i‖ ≤ LA)
    (hXA' : ∀ i, ‖XA' i‖ ≤ LA)
    (hXAdiff : ∀ i, ‖XA i - XA' i‖ ≤ ε * LA)
    (hXB : ∀ i, ‖XB i‖ ≤ LB)
    (hXB' : ∀ i, ‖XB' i‖ ≤ LB)
    (hXBdiff : ∀ i, ‖XB i - XB' i‖ ≤ ε * LB)
    (hYAB : ∀ i, ‖YAB i‖ ≤ LA * LB)
    (hYAB' : ∀ i, ‖YAB' i‖ ≤ LA * LB)
    (hYABdiff : ∀ i, ‖YAB i - YAB' i‖ ≤ ε * (LA * LB)) :
    ‖fourFactorMixed W XA XB YAB -
        fourFactorMixed W' XA' XB' YAB'‖ ≤
      64 * ε * LA * LB := by
  have hLAB : 0 ≤ LA * LB := mul_nonneg hLA hLB
  let F := fourFactorMixedFactors W XA XB YAB
  let F' := fourFactorMixedFactors W' XA' XB' YAB'
  have ht0 :
      ‖fourMatrixProduct (F 0) - fourMatrixProduct (F' 0)‖ ≤
        4 * ε * (LA * LB) := by
    simpa [F, F', fourFactorMixedFactors] using
      norm_fourMatrixProduct_sub_le_four_scales
        (F 0) (F' 0) (LA * LB) 1 1 1 ε hε hLAB
        (by norm_num) (by norm_num) (by norm_num)
        (hYAB 0) (hW 1) (hW 2) (hW 3)
        (hYAB' 0) (hW' 1) (hW' 2) (hW' 3)
        (hYABdiff 0) (by simpa using hWdiff 1)
        (by simpa using hWdiff 2) (by simpa using hWdiff 3)
  have ht1 :
      ‖fourMatrixProduct (F 1) - fourMatrixProduct (F' 1)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 1) (F' 1) LA LB 1 1 ε hε hLA hLB
      (by norm_num) (by norm_num)
      (hXA 0) (hXB 1) (hW 2) (hW 3)
      (hXA' 0) (hXB' 1) (hW' 2) (hW' 3)
      (hXAdiff 0) (hXBdiff 1)
      (by simpa using hWdiff 2) (by simpa using hWdiff 3) using 1 <;> ring
  have ht2 :
      ‖fourMatrixProduct (F 2) - fourMatrixProduct (F' 2)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 2) (F' 2) LB LA 1 1 ε hε hLB hLA
      (by norm_num) (by norm_num)
      (hXB 0) (hXA 1) (hW 2) (hW 3)
      (hXB' 0) (hXA' 1) (hW' 2) (hW' 3)
      (hXBdiff 0) (hXAdiff 1)
      (by simpa using hWdiff 2) (by simpa using hWdiff 3) using 1 <;> ring
  have ht3 :
      ‖fourMatrixProduct (F 3) - fourMatrixProduct (F' 3)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 3) (F' 3) LA 1 LB 1 ε hε hLA
      (by norm_num) hLB (by norm_num)
      (hXA 0) (hW 1) (hXB 2) (hW 3)
      (hXA' 0) (hW' 1) (hXB' 2) (hW' 3)
      (hXAdiff 0) (by simpa using hWdiff 1)
      (hXBdiff 2) (by simpa using hWdiff 3) using 1 <;> ring
  have ht4 :
      ‖fourMatrixProduct (F 4) - fourMatrixProduct (F' 4)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 4) (F' 4) LB 1 LA 1 ε hε hLB
      (by norm_num) hLA (by norm_num)
      (hXB 0) (hW 1) (hXA 2) (hW 3)
      (hXB' 0) (hW' 1) (hXA' 2) (hW' 3)
      (hXBdiff 0) (by simpa using hWdiff 1)
      (hXAdiff 2) (by simpa using hWdiff 3) using 1 <;> ring
  have ht5 :
      ‖fourMatrixProduct (F 5) - fourMatrixProduct (F' 5)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 5) (F' 5) LA 1 1 LB ε hε hLA
      (by norm_num) (by norm_num) hLB
      (hXA 0) (hW 1) (hW 2) (hXB 3)
      (hXA' 0) (hW' 1) (hW' 2) (hXB' 3)
      (hXAdiff 0) (by simpa using hWdiff 1)
      (by simpa using hWdiff 2) (hXBdiff 3) using 1 <;> ring
  have ht6 :
      ‖fourMatrixProduct (F 6) - fourMatrixProduct (F' 6)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 6) (F' 6) LB 1 1 LA ε hε hLB
      (by norm_num) (by norm_num) hLA
      (hXB 0) (hW 1) (hW 2) (hXA 3)
      (hXB' 0) (hW' 1) (hW' 2) (hXA' 3)
      (hXBdiff 0) (by simpa using hWdiff 1)
      (by simpa using hWdiff 2) (hXAdiff 3) using 1 <;> ring
  have ht7 :
      ‖fourMatrixProduct (F 7) - fourMatrixProduct (F' 7)‖ ≤
        4 * ε * (LA * LB) := by
    simpa [F, F', fourFactorMixedFactors] using
      norm_fourMatrixProduct_sub_le_four_scales
        (F 7) (F' 7) 1 (LA * LB) 1 1 ε hε (by norm_num) hLAB
        (by norm_num) (by norm_num)
        (hW 0) (hYAB 1) (hW 2) (hW 3)
        (hW' 0) (hYAB' 1) (hW' 2) (hW' 3)
        (by simpa using hWdiff 0) (hYABdiff 1)
        (by simpa using hWdiff 2) (by simpa using hWdiff 3)
  have ht8 :
      ‖fourMatrixProduct (F 8) - fourMatrixProduct (F' 8)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 8) (F' 8) 1 LA LB 1 ε hε (by norm_num) hLA hLB
      (by norm_num)
      (hW 0) (hXA 1) (hXB 2) (hW 3)
      (hW' 0) (hXA' 1) (hXB' 2) (hW' 3)
      (by simpa using hWdiff 0) (hXAdiff 1)
      (hXBdiff 2) (by simpa using hWdiff 3) using 1 <;> ring
  have ht9 :
      ‖fourMatrixProduct (F 9) - fourMatrixProduct (F' 9)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 9) (F' 9) 1 LB LA 1 ε hε (by norm_num) hLB hLA
      (by norm_num)
      (hW 0) (hXB 1) (hXA 2) (hW 3)
      (hW' 0) (hXB' 1) (hXA' 2) (hW' 3)
      (by simpa using hWdiff 0) (hXBdiff 1)
      (hXAdiff 2) (by simpa using hWdiff 3) using 1 <;> ring
  have ht10 :
      ‖fourMatrixProduct (F 10) - fourMatrixProduct (F' 10)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 10) (F' 10) 1 LA 1 LB ε hε (by norm_num) hLA
      (by norm_num) hLB
      (hW 0) (hXA 1) (hW 2) (hXB 3)
      (hW' 0) (hXA' 1) (hW' 2) (hXB' 3)
      (by simpa using hWdiff 0) (hXAdiff 1)
      (by simpa using hWdiff 2) (hXBdiff 3) using 1 <;> ring
  have ht11 :
      ‖fourMatrixProduct (F 11) - fourMatrixProduct (F' 11)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 11) (F' 11) 1 LB 1 LA ε hε (by norm_num) hLB
      (by norm_num) hLA
      (hW 0) (hXB 1) (hW 2) (hXA 3)
      (hW' 0) (hXB' 1) (hW' 2) (hXA' 3)
      (by simpa using hWdiff 0) (hXBdiff 1)
      (by simpa using hWdiff 2) (hXAdiff 3) using 1 <;> ring
  have ht12 :
      ‖fourMatrixProduct (F 12) - fourMatrixProduct (F' 12)‖ ≤
        4 * ε * (LA * LB) := by
    simpa [F, F', fourFactorMixedFactors] using
      norm_fourMatrixProduct_sub_le_four_scales
        (F 12) (F' 12) 1 1 (LA * LB) 1 ε hε
        (by norm_num) (by norm_num) hLAB (by norm_num)
        (hW 0) (hW 1) (hYAB 2) (hW 3)
        (hW' 0) (hW' 1) (hYAB' 2) (hW' 3)
        (by simpa using hWdiff 0) (by simpa using hWdiff 1)
        (hYABdiff 2) (by simpa using hWdiff 3)
  have ht13 :
      ‖fourMatrixProduct (F 13) - fourMatrixProduct (F' 13)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 13) (F' 13) 1 1 LA LB ε hε (by norm_num) (by norm_num)
      hLA hLB
      (hW 0) (hW 1) (hXA 2) (hXB 3)
      (hW' 0) (hW' 1) (hXA' 2) (hXB' 3)
      (by simpa using hWdiff 0) (by simpa using hWdiff 1)
      (hXAdiff 2) (hXBdiff 3) using 1 <;> ring
  have ht14 :
      ‖fourMatrixProduct (F 14) - fourMatrixProduct (F' 14)‖ ≤
        4 * ε * (LA * LB) := by
    convert norm_fourMatrixProduct_sub_le_four_scales
      (F 14) (F' 14) 1 1 LB LA ε hε (by norm_num) (by norm_num)
      hLB hLA
      (hW 0) (hW 1) (hXB 2) (hXA 3)
      (hW' 0) (hW' 1) (hXB' 2) (hXA' 3)
      (by simpa using hWdiff 0) (by simpa using hWdiff 1)
      (hXBdiff 2) (hXAdiff 3) using 1 <;> ring
  have ht15 :
      ‖fourMatrixProduct (F 15) - fourMatrixProduct (F' 15)‖ ≤
        4 * ε * (LA * LB) := by
    simpa [F, F', fourFactorMixedFactors] using
      norm_fourMatrixProduct_sub_le_four_scales
        (F 15) (F' 15) 1 1 1 (LA * LB) ε hε
        (by norm_num) (by norm_num) (by norm_num) hLAB
        (hW 0) (hW 1) (hW 2) (hYAB 3)
        (hW' 0) (hW' 1) (hW' 2) (hYAB' 3)
        (by simpa using hWdiff 0) (by simpa using hWdiff 1)
        (by simpa using hWdiff 2) (hYABdiff 3)
  rw [fourFactorMixed_eq_sum_products, fourFactorMixed_eq_sum_products]
  have hsum :
      (∑ i : Fin 16,
          fourMatrixProduct (fourFactorMixedFactors W XA XB YAB i)) -
        (∑ i : Fin 16,
          fourMatrixProduct
            (fourFactorMixedFactors W' XA' XB' YAB' i)) =
      ∑ i : Fin 16,
        (fourMatrixProduct (fourFactorMixedFactors W XA XB YAB i) -
          fourMatrixProduct
            (fourFactorMixedFactors W' XA' XB' YAB' i)) := by
    symm
    exact Finset.sum_sub_distrib
      (s := (Finset.univ : Finset (Fin 16)))
      (fun i =>
        fourMatrixProduct (fourFactorMixedFactors W XA XB YAB i))
      (fun i =>
        fourMatrixProduct (fourFactorMixedFactors W' XA' XB' YAB' i))
  rw [hsum]
  calc
    ‖∑ i : Fin 16,
        (fourMatrixProduct (fourFactorMixedFactors W XA XB YAB i) -
          fourMatrixProduct
            (fourFactorMixedFactors W' XA' XB' YAB' i))‖
        ≤ ∑ i : Fin 16,
          ‖fourMatrixProduct (fourFactorMixedFactors W XA XB YAB i) -
            fourMatrixProduct
              (fourFactorMixedFactors W' XA' XB' YAB' i)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _i : Fin 16, 4 * ε * (LA * LB) := by
      apply Finset.sum_le_sum
      intro i hi
      fin_cases i
      · simpa [F, F'] using ht0
      · simpa [F, F'] using ht1
      · simpa [F, F'] using ht2
      · simpa [F, F'] using ht3
      · simpa [F, F'] using ht4
      · simpa [F, F'] using ht5
      · simpa [F, F'] using ht6
      · simpa [F, F'] using ht7
      · simpa [F, F'] using ht8
      · simpa [F, F'] using ht9
      · simpa [F, F'] using ht10
      · simpa [F, F'] using ht11
      · simpa [F, F'] using ht12
      · simpa [F, F'] using ht13
      · simpa [F, F'] using ht14
      · simpa [F, F'] using ht15
    _ = 64 * ε * LA * LB := by
      simp
      ring

end

end YangMills.RG
