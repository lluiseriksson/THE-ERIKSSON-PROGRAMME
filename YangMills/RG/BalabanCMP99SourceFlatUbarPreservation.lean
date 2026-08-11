/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatPhysicalTransport

/-!
# Preservation of the flat background by the physical Ubar map

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

The source-generated next background is not caller data.  This file proves
the first dictionary needed to compare the generated physical tower with the
literal flat Fourier operator: when every fine link is one, every contour
deviation is one, the averaged logarithmic exponent is zero, and physical
Ubar reconstructs the flat coarse gauge configuration.

Honest scope: this is the exact one-scale flat-background statement for the
direct deviation-budget constructor.  It does not yet construct a complete
source-normalized tower, identify its iterated `Q'`, or compare Lean's
counting adjoint with the printed weighted adjoint.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The straight coarse transport generated from the flat fine background is
one on every positive coarse bond. -/
@[simp] theorem cmp99SourceBaseCoarseBackground_flat_apply_pos
    (b : PhysicalBond d N') :
    cmp99SourceBaseCoarseBackground
        (cmp99SourceFlatGaugeConfig d (M * N') Nc)
        (positiveEdgeOfPhysicalBond b) = 1 := by
  rw [cmp99SourceBaseCoarseBackground_apply_pos]
  change wilsonLine (cmp99SourceFlatGaugeConfig d (M * N') Nc) _ = 1
  exact wilsonLine_cmp99SourceFlatGaugeConfig _

/-- Every four-contour deviation entering physical Ubar is one in the flat
background.  No path geometry is needed beyond the fact that every fine
Wilson line is one. -/
@[simp] theorem UbarDeviation_cmp99SourceFlatGaugeConfig
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (Γ_1 Γ_2 Γ_3 : FinBox d (M * N') →
      List (FiniteLatticeGeometry.E
        (d := d) (N := M * N') (G := SUN Nc))) :
    UbarDeviation
        (cmp99SourceFlatGaugeConfig d (M * N') Nc)
        (cmp99SourceBaseCoarseBackground
          (cmp99SourceFlatGaugeConfig d (M * N') Nc))
        (positiveEdgeOfPhysicalBond b) x Γ_1 Γ_2 Γ_3 = 1 := by
  unfold UbarDeviation
  simp

/-- A finite physical Ubar exponent vanishes when every special-unitary
deviation in its support is one. -/
theorem cmp99UbarSpecialUnitaryExponent_eq_zero_of_eq_one
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (hD : ∀ i ∈ s, D i = 1) :
    cmp99UbarSpecialUnitaryExponent s w D = 0 := by
  simp [cmp99UbarSpecialUnitaryExponent, cmp99UbarUnitaryExponent,
    cmp99UbarExponent, hD]

/-- The direct deviation-budget Ubar block is one in the literal flat
background.  The budget and its proof certify that the constructor is legal;
they do not affect the resulting zero exponent. -/
@[simp] theorem cmp99PhysicalUbarBlockOfDeviationBudget_flat
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (M * N') →
      List (FiniteLatticeGeometry.E
        (d := d) (N := M * N') (G := SUN Nc)))
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          (cmp99SourceFlatGaugeConfig d (M * N') Nc)
          (cmp99SourceBaseCoarseBackground
            (cmp99SourceFlatGaugeConfig d (M * N') Nc))
          (positiveEdgeOfPhysicalBond b) x
          (Γ_1 b) (Γ_2 b) (Γ_3 b)‖ ≤ B.δ)
    (b : PhysicalBond d N') :
    cmp99PhysicalUbarBlockOfDeviationBudget
        (cmp99SourceFlatGaugeConfig d (M * N') Nc)
        (cmp99SourceBaseCoarseBackground
          (cmp99SourceFlatGaugeConfig d (M * N') Nc))
        Γ_1 Γ_2 Γ_3 B hdev b = 1 := by
  unfold cmp99PhysicalUbarBlockOfDeviationBudget
  dsimp only
  apply Subtype.ext
  rw [cmp99UbarSpecialUnitaryBlockOfDeviationBudget_coe]
  rw [cmp99UbarSpecialUnitaryExponent_eq_zero_of_eq_one]
  · simp
  · intro x hx
    exact UbarDeviation_cmp99SourceFlatGaugeConfig b x
      (Γ_1 b) (Γ_2 b) (Γ_3 b)

/-- The complete oriented physical Ubar background is the literal flat
coarse configuration.  Negative orientations are covered by the exact
positive-bond reconstruction, not by an independent hypothesis. -/
theorem cmp99PhysicalUbarGaugeConfigOfDeviationBudget_flat
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (M * N') →
      List (FiniteLatticeGeometry.E
        (d := d) (N := M * N') (G := SUN Nc)))
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          (cmp99SourceFlatGaugeConfig d (M * N') Nc)
          (cmp99SourceBaseCoarseBackground
            (cmp99SourceFlatGaugeConfig d (M * N') Nc))
          (positiveEdgeOfPhysicalBond b) x
          (Γ_1 b) (Γ_2 b) (Γ_3 b)‖ ≤ B.δ) :
    cmp99PhysicalUbarGaugeConfigOfDeviationBudget
        (cmp99SourceFlatGaugeConfig d (M * N') Nc)
        (cmp99SourceBaseCoarseBackground
          (cmp99SourceFlatGaugeConfig d (M * N') Nc))
        Γ_1 Γ_2 Γ_3 B hdev =
      cmp99SourceFlatGaugeConfig d N' Nc := by
  apply gaugeConfig_ext
  intro e
  cases e with
  | mk y μ sign =>
      cases sign <;>
        simp [cmp99PhysicalUbarGaugeConfigOfDeviationBudget,
          gaugeConfigOfPositiveBonds, cmp99SourceFlatGaugeConfig]

end

end YangMills.RG
