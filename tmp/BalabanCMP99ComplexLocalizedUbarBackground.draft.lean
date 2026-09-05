import YangMills.RG.BalabanCMP99ComplexUbarSpecialLinear
import YangMills.RG.BalabanCMP99SourceUbarContours

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# One literal analytic CMP99 Ubar background step

The source contours and base coarse background are already group-generic.
This module specializes them to `SL(N,C)`, constructs every positive coarse
bond from the determinant-one complex Ubar factor, and reconstructs negative
orientations canonically.  The only analytic premise left visible is the
uniform deviation budget for the literal path product itself.

It does not accept a preselected coarse background, a free Ubar block, or a
scale-indexed background family.  It is one step only; the forced finite
recursion and the producer of its deviation bound remain open.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local notation "SLNc" => Matrix.SpecialLinearGroup (Fin Nc) ℂ

/-- The literal source deviation on one analytic coarse bond. -/
def cmp99SourceComplexLocalizedUbarDeviation
    (background : GaugeConfig d (M * N') SLNc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) : SLNc :=
  UbarDeviation background (cmp99SourceBaseCoarseBackground background)
    (positiveEdgeOfPhysicalBond b) x
    (cmp99SourceUbarGamma1 (G := SLNc) b)
    (cmp99SourceUbarGamma2 (G := SLNc) b)
    (cmp99SourceUbarGamma3 (G := SLNc) b)

/-- One positive-bond analytic Ubar value with the exact source mass
`M^{-d}`.  The scalar budget supplies the Mercator and no-winding gates. -/
noncomputable def cmp99SourceComplexLocalizedUbarBlock
    (background : GaugeConfig d (M * N') SLNc)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖(cmp99SourceComplexLocalizedUbarDeviation background b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (b : PhysicalBond d N') : SLNc :=
  cmp99UbarSpecialLinearBlockOfDeviationBudget
    (blockOf M N' b.1) (fun _ => (M ^ d : ℝ)⁻¹)
    (cmp99SourceComplexLocalizedUbarDeviation background b) B
    (hdev b)
    (cmp99SourceBaseCoarseBackground background
      (positiveEdgeOfPhysicalBond b))

/-- The complete oriented analytic next background.  Every coarse value is
generated from the fine background; no caller-supplied coarse family occurs. -/
noncomputable def cmp99SourceComplexLocalizedNextBackground
    (background : GaugeConfig d (M * N') SLNc)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖(cmp99SourceComplexLocalizedUbarDeviation background b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ) :
    GaugeConfig d N' SLNc :=
  gaugeConfigOfPositiveBonds fun b =>
    cmp99SourceComplexLocalizedUbarBlock background B hdev b

@[simp] theorem cmp99SourceComplexLocalizedNextBackground_apply_pos
    (background : GaugeConfig d (M * N') SLNc)
    (B : MatrixNearLogNoWindingBudget Nc) (hdev)
    (b : PhysicalBond d N') :
    cmp99SourceComplexLocalizedNextBackground background B hdev
        (positiveEdgeOfPhysicalBond b) =
      cmp99SourceComplexLocalizedUbarBlock background B hdev b := by
  exact gaugeConfigOfPositiveBonds_apply_pos _ b

end

end YangMills.RG
