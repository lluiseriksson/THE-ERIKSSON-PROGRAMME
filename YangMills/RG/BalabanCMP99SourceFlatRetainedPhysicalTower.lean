/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatNormalizedScale
import YangMills.RG.BalabanCMP99SourceRetainedPhysicalTower
import YangMills.RG.BalabanCMP99SourceUbarRadiusBudget

/-!
# The generated retained CMP99 tower at the flat background

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

The scalar Ubar radius recursion fixes zero exactly.  Consequently one closed
zero-radius budget constructs the entire former proof-valued radius chain,
and the physical retained-tower constructor can be run on the literal flat
background without a caller-supplied smallness family.

Honest scope: this file materializes the canonical generated retained tower.
It does not yet identify every hidden intermediate background with the flat
configuration, identify the retained `Q'` with the printed flat block average,
or bridge counting and weighted adjoints.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {d M N Nc : ℕ}
variable [hd0 : NeZero d] [hM0 : NeZero M] [hN0 : NeZero N]
variable [hNc0 : NeZero Nc]

/-- Zero is a fixed point of the exact one-step source Ubar radius map. -/
@[simp] theorem cmp99SourceUbarNextFineRadius_zero :
    cmp99SourceUbarNextFineRadius d M 0 = 0 := by
  simp [cmp99SourceUbarNextFineRadius, cmp99SourceUbarFineDeviationRadius]

/-- Every radius in the source recursion remains literally zero when the
initial fine-link radius is zero. -/
@[simp] theorem cmp99SourceUbarRadiusAt_zero_radius (k : ℕ) :
    cmp99SourceUbarRadiusAt d M 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [cmp99SourceUbarRadiusAt_succ, ih,
        cmp99SourceUbarNextFineRadius_zero]

/-- A single closed scalar budget for an arbitrary-depth zero-radius source
tower. -/
def cmp99SourceFlatZeroClosedBudget (depth : ℕ) :
    CMP99SourceUbarClosedBudget d M Nc depth 0 where
  epsilon_nonneg := le_rfl
  terminal_small := by
    simp only [mul_zero]
    rw [lt_min_iff]
    exact ⟨cmp99UbarNoWindingThreshold_pos, by norm_num⟩

/-- The complete proof-valued Ubar chain generated from the one closed
zero-radius budget. -/
theorem cmp99SourceFlatZeroRadiusChain (depth : ℕ) :
    CMP99SourceUbarRadiusChain d M Nc depth 0 :=
  (cmp99SourceFlatZeroClosedBudget depth).toRadiusChain

/-- The canonical retained physical source tower generated from the literal
flat fine background and the internally constructed zero-radius chain. -/
noncomputable def cmp99SourceFlatRetainedPhysicalTower
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing : ℝ) :
    CMP99SourceRetainedPhysicalTower rho
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
      M spacing
      (cmp99SourceFlatGaugeConfig d
        (cmp99RegionalLatticeSize M N depth) Nc)
      depth :=
  cmp99SourceRetainedPhysicalTower hd hM rho Omega depth spacing 0
    (cmp99SourceFlatGaugeConfig d (cmp99RegionalLatticeSize M N depth) Nc)
    (cmp99SourceFlatZeroRadiusChain depth)
    (by
      intro e
      simp)

end

end YangMills.RG
