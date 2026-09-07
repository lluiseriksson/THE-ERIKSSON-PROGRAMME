/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexQuadraticSchur

/-!
# Scalar defect budget for the complex `R1` telescope

The exact bilateral `R1` budget contains the full contour matrices `G1` and
`C1`.  They are not independent: `G1 = G0 + R3` and `C1 = C0 + E`.
This module performs that substitution once and bounds the entire telescope
by eight row/column constants for the two base matrices and the two literal
defects.  Thus later source work only has to estimate physical base
operators and contour defects, never the full matrices separately.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

/-- Bilateral scalar budget after replacing the full contour matrices by
their base-plus-defect decompositions. -/
def cmp116R1TelescopeDefectBilateralBudget
    (g0Row g0Column c0Row c0Column
      r3Row r3Column covarianceDefectRow covarianceDefectColumn : ℝ) : ℝ :=
  let g1Row := g0Row + r3Row
  let g1Column := g0Column + r3Column
  let c1Row := c0Row + covarianceDefectRow
  let c1Column := c0Column + covarianceDefectColumn
  ((r3Column * c1Row * g1Row +
      g0Column * covarianceDefectRow * g1Row +
      g0Column * c0Row * r3Row) +
    (g1Column * c1Column * r3Row +
      g1Column * covarianceDefectColumn * g0Row +
      r3Column * c0Column * g0Row)) / 4

/-- The exact telescope budget is controlled by row and column estimates of
the base Gamma/covariance and the literal Gamma/covariance defects. -/
theorem cmp116R1TelescopeBilateralSchurBudget_le_defectBudget
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (G0 G1 C0 C1 : Matrix ι ι ℂ)
    {g0Row g0Column c0Row c0Column
      r3Row r3Column covarianceDefectRow covarianceDefectColumn : ℝ}
    (hg0Row : ‖G0‖ ≤ g0Row)
    (hg0Column : ‖G0.transpose‖ ≤ g0Column)
    (hc0Row : ‖C0‖ ≤ c0Row)
    (hc0Column : ‖C0.transpose‖ ≤ c0Column)
    (hr3Row : ‖G1 - G0‖ ≤ r3Row)
    (hr3Column : ‖(G1 - G0).transpose‖ ≤ r3Column)
    (hcovRow : ‖C1 - C0‖ ≤ covarianceDefectRow)
    (hcovColumn : ‖(C1 - C0).transpose‖ ≤ covarianceDefectColumn) :
    cmp116R1TelescopeBilateralSchurBudget G0 G1 C0 C1 ≤
      cmp116R1TelescopeDefectBilateralBudget
        g0Row g0Column c0Row c0Column
        r3Row r3Column covarianceDefectRow covarianceDefectColumn := by
  have hg0Row0 : 0 ≤ g0Row := (norm_nonneg G0).trans hg0Row
  have hg0Column0 : 0 ≤ g0Column :=
    (norm_nonneg G0.transpose).trans hg0Column
  have hc0Row0 : 0 ≤ c0Row := (norm_nonneg C0).trans hc0Row
  have hc0Column0 : 0 ≤ c0Column :=
    (norm_nonneg C0.transpose).trans hc0Column
  have hr3Row0 : 0 ≤ r3Row := (norm_nonneg (G1 - G0)).trans hr3Row
  have hr3Column0 : 0 ≤ r3Column :=
    (norm_nonneg (G1 - G0).transpose).trans hr3Column
  have hcovRow0 : 0 ≤ covarianceDefectRow :=
    (norm_nonneg (C1 - C0)).trans hcovRow
  have hcovColumn0 : 0 ≤ covarianceDefectColumn :=
    (norm_nonneg (C1 - C0).transpose).trans hcovColumn
  have hg1Row : ‖G1‖ ≤ g0Row + r3Row := by
    calc
      ‖G1‖ = ‖G0 + (G1 - G0)‖ := by
        congr 1
        abel
      _ ≤ ‖G0‖ + ‖G1 - G0‖ := norm_add_le _ _
      _ ≤ g0Row + r3Row := add_le_add hg0Row hr3Row
  have hg1Column : ‖G1.transpose‖ ≤ g0Column + r3Column := by
    calc
      ‖G1.transpose‖ =
          ‖G0.transpose + (G1 - G0).transpose‖ := by
            congr 1
            ext i j
            simp
      _ ≤ ‖G0.transpose‖ + ‖(G1 - G0).transpose‖ := norm_add_le _ _
      _ ≤ g0Column + r3Column := add_le_add hg0Column hr3Column
  have hc1Row : ‖C1‖ ≤ c0Row + covarianceDefectRow := by
    calc
      ‖C1‖ = ‖C0 + (C1 - C0)‖ := by
        congr 1
        abel
      _ ≤ ‖C0‖ + ‖C1 - C0‖ := norm_add_le _ _
      _ ≤ c0Row + covarianceDefectRow := add_le_add hc0Row hcovRow
  have hc1Column :
      ‖C1.transpose‖ ≤ c0Column + covarianceDefectColumn := by
    calc
      ‖C1.transpose‖ =
          ‖C0.transpose + (C1 - C0).transpose‖ := by
            congr 1
            ext i j
            simp
      _ ≤ ‖C0.transpose‖ + ‖(C1 - C0).transpose‖ := norm_add_le _ _
      _ ≤ c0Column + covarianceDefectColumn :=
        add_le_add hc0Column hcovColumn
  unfold cmp116R1TelescopeBilateralSchurBudget
    cmp116R1TelescopeDefectBilateralBudget
  dsimp only
  gcongr

end

end YangMills.RG
