/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214CauchyMajorant

/-!
# Product form of the CMP116 Cauchy loss

The recursive loss used for the two contour families in equation (2.14) is
exactly division by the product of their radii.  Consequently, comparison of
the canonical Cauchy term weight with the literal equation-(2.26) ledger can
be proved before Cauchy extraction: the boundary majorant must contain the
ledger times the two radius products.  This is strictly weaker and more
source-faithful than assuming the final term-weight comparison itself.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Closed product formula for the recursively defined Cauchy loss. -/
theorem cmp116Eq214CauchyRate_eq_div_prod
    (n : ℕ) (radius : Fin n → ℝ) (majorant : ℝ) :
    cmp116Eq214CauchyRate n radius majorant =
      majorant / ∏ i, radius i := by
  induction n with
  | zero => simp [cmp116Eq214CauchyRate]
  | succ n ih =>
      simp only [cmp116Eq214CauchyRate]
      rw [ih]
      rw [Fin.prod_univ_succ]
      ring

/-- The nested `sigma`/`tau` Cauchy loss is division by the product of both
source radius families. -/
theorem cmp116Eq214NestedCauchyRate_eq_div_prod
    (nDelta nY : ℕ)
    (deltaRadius : Fin nDelta → ℝ) (yRadius : Fin nY → ℝ)
    (majorant : ℝ) :
    cmp116Eq214CauchyRate nDelta deltaRadius
        (cmp116Eq214CauchyRate nY yRadius majorant) =
      majorant /
        ((∏ i, deltaRadius i) * (∏ i, yRadius i)) := by
  rw [cmp116Eq214CauchyRate_eq_div_prod,
    cmp116Eq214CauchyRate_eq_div_prod]
  ring

/-- Source-facing comparison principle for equation (2.26).

Instead of receiving the post-Cauchy conclusion as a premise, it asks for the
physical boundary majorant to be bounded by the target ledger times exactly
the radii that the two Cauchy families consume. -/
theorem cmp116Eq214CauchyTermWeight_le_of_boundaryMajorant_le_mul_radiusProduct
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (boundaryMajorant sourceLedger : ℝ)
    (hDelta : ∀ i, 0 < A.deltaRadius i)
    (hY : ∀ i, 0 < A.yRadius i)
    (hboundary :
      boundaryMajorant ≤
        sourceLedger *
          ((∏ i, A.deltaRadius i) * (∏ i, A.yRadius i))) :
    cmp116Eq214CauchyTermWeight A boundaryMajorant ≤ sourceLedger := by
  have hDeltaProd : 0 < ∏ i, A.deltaRadius i := by
    exact Finset.prod_pos fun i _ => hDelta i
  have hYProd : 0 < ∏ i, A.yRadius i := by
    exact Finset.prod_pos fun i _ => hY i
  have hProd :
      0 < (∏ i, A.deltaRadius i) * (∏ i, A.yRadius i) :=
    mul_pos hDeltaProd hYProd
  unfold cmp116Eq214CauchyTermWeight
  rw [cmp116Eq214NestedCauchyRate_eq_div_prod]
  exact (div_le_iff₀ hProd).2 (by simpa [mul_assoc] using hboundary)

end

end YangMills.RG
