/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226SourceLedger

/-!
# The source `sigma(Delta)` Cauchy loss in CMP116 equation (2.26)

CMP116 takes the outer circles to be `|sigma(Delta)| = exp kappa1`, while
the interpolation point lies in `[0,1]`.  The source bound uses the uniform
working radius `exp (kappa1 - 1)` for the centered Cauchy estimate.  Iterating
that radius gives exactly the gap factor

`exp (-(kappa1 - 1) * (L*M)^(-4) * |Z \ Z0'|)`

once the physical count of outer variables is identified with the normalized
gap cardinality.  The latter identification remains an explicit geometric
premise; no post-Cauchy term bound is assumed.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Uniform centered radius used for each outer `sigma(Delta)` derivative. -/
def cmp116Eq214SigmaCauchyRadius (kappa1 : ℝ) : ℝ :=
  Real.exp (kappa1 - 1)

theorem cmp116Eq214SigmaCauchyRadius_pos (kappa1 : ℝ) :
    0 < cmp116Eq214SigmaCauchyRadius kappa1 := by
  unfold cmp116Eq214SigmaCauchyRadius
  positivity

/-- Product of the source working radii over all outer coordinates. -/
theorem cmp116Eq214SigmaCauchyRadius_prod (n : ℕ) (kappa1 : ℝ) :
    (∏ _ : Fin n, cmp116Eq214SigmaCauchyRadius kappa1) =
      Real.exp ((kappa1 - 1) * (n : ℝ)) := by
  calc
    (∏ _ : Fin n, cmp116Eq214SigmaCauchyRadius kappa1) =
        Real.exp (kappa1 - 1) ^ n := by
          simp [cmp116Eq214SigmaCauchyRadius]
    _ = Real.exp ((n : ℝ) * (kappa1 - 1)) :=
      (Real.exp_nat_mul (kappa1 - 1) n).symm
    _ = Real.exp ((kappa1 - 1) * (n : ℝ)) := by
      congr 1
      ring

/-- Exact consumption of the outer Cauchy family by the first factor of
equation (2.26).  `hnormalizedGap` is precisely the geometric dictionary
`#Delta = (L*M)^(-4) * |Z \ Z0'|`. -/
theorem cmp116Eq214SigmaCauchyRate_eq_mul_gapFactor
    (n : ℕ) (kappa1 majorant : ℝ) (L M gapCard : ℕ)
    (hnormalizedGap :
      ((((L * M : ℕ) : ℝ) ^ 4)⁻¹ * (gapCard : ℝ)) = (n : ℝ)) :
    cmp116Eq214CauchyRate n
        (fun _ => cmp116Eq214SigmaCauchyRadius kappa1) majorant =
      majorant * cmp116Eq226GapFactor kappa1 L M gapCard := by
  rw [cmp116Eq214CauchyRate_eq_div_prod,
    cmp116Eq214SigmaCauchyRadius_prod]
  unfold cmp116Eq226GapFactor
  have hexponent :
      -((kappa1 - 1) * (((L * M : ℕ) : ℝ) ^ 4)⁻¹ *
          (gapCard : ℝ)) =
        -((kappa1 - 1) * (n : ℝ)) := by
    rw [mul_assoc, hnormalizedGap]
  rw [hexponent]
  rw [div_eq_mul_inv, ← Real.exp_neg]

/-- The same identity in data-facing form: once `deltaRadius` is the source
radius family, the remaining outer rate is literally the gap factor. -/
theorem cmp116Eq214CauchyRate_eq_mul_gapFactor_of_deltaRadius
    {n : ℕ} (deltaRadius : Fin n → ℝ)
    (kappa1 majorant : ℝ) (L M gapCard : ℕ)
    (hRadius : deltaRadius = fun _ => cmp116Eq214SigmaCauchyRadius kappa1)
    (hnormalizedGap :
      ((((L * M : ℕ) : ℝ) ^ 4)⁻¹ * (gapCard : ℝ)) = (n : ℝ)) :
    cmp116Eq214CauchyRate n deltaRadius majorant =
      majorant * cmp116Eq226GapFactor kappa1 L M gapCard := by
  rw [hRadius]
  exact cmp116Eq214SigmaCauchyRate_eq_mul_gapFactor
    n kappa1 majorant L M gapCard hnormalizedGap

end

end YangMills.RG
