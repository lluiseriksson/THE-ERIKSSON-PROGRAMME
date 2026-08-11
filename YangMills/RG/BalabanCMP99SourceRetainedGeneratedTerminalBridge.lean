/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatRetainedPhysicalTower
import YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime

/-!
PRE-VALIDATION: source present; `.olean` not yet materialized and these
declarations have not yet been verified by the Lean compiler.

# The retained terminal prefix is the generated `Q'` tower

The retained physical construction and the typed active-region-chain
construction recurse through the same physical `Ubar` backgrounds and the
same transported one-step averages.  This file identifies the last retained
prefix with the already-consumed generated `weightedQprimeTower`; it does not
introduce a second family of `Q'` operators or an equality supplied by a
caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The last prefix retained by the physical recursive constructor is
literally the tower generated on the canonical typed active-region chain. -/
theorem cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    (cmp99SourceGeneratedRetainedPhysicalTower hd hM rho Omega depth
      spacing epsilon background chain fineSmall).towerAt (Fin.last depth) =
      (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
        |>.weightedQprimeTower hd hM rho spacing epsilon background chain
          fineSmall) := by
  rfl

/-- At the literal flat background, the terminal retained prefix is therefore
the canonical generated `Q'` tower used by the CMP99 transition, mass,
precision, and covariance consumers. -/
theorem cmp99SourceFlatRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) (spacing : ℝ) :
    (cmp99SourceFlatRetainedPhysicalTower hd hM rho Omega depth spacing).towerAt
        (Fin.last depth) =
      (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
        |>.weightedQprimeTower hd hM rho spacing 0
          (cmp99SourceFlatGaugeConfig d
            (cmp99RegionalLatticeSize M N depth) Nc)
          (cmp99SourceFlatZeroRadiusChain depth)
          (by
            intro e
            change ‖((1 : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0
            simp)) := by
  exact
    cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower
      hd hM rho Omega depth spacing 0
      (cmp99SourceFlatGaugeConfig d
        (cmp99RegionalLatticeSize M N depth) Nc)
      (cmp99SourceFlatZeroRadiusChain depth) _

end

end YangMills.RG
