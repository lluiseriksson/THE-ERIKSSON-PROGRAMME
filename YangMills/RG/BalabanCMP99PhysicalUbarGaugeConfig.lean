/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99UbarPhysicalDeviation
import YangMills.RG.BalabanCMP99UbarDeviationBudget
import YangMills.RG.BalabanCMP116WilsonHessianLiteral

/-!
# The physical CMP99 Ubar gauge configuration

The canonical physical deviation budget is consumed here to construct one
special-unitary Ubar block on every positive coarse bond.  The existing exact
positive-bond reconstruction then supplies negative orientations by inversion,
so the result is a literal `GaugeConfig` rather than an unoriented family.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {d N' L Nc : ℕ} [NeZero d] [NeZero N'] [NeZero L] [NeZero Nc]

local notation "FineEdge" =>
  FiniteLatticeGeometry.E (d := d) (N := L * N') (G := SUN Nc)

/-- The special-unitary Ubar value on one positive coarse bond, constructed
only from literal deviations and the explicit scalar threshold. -/
noncomputable def cmp99PhysicalUbarBlock
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d L ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ∀ e, (e ∈ Γ_1 b x ∨ e ∈ Γ_2 b x ∨ e ∈ Γ_3 b x) →
        ‖(A_fine e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ ε)
    (hcoarse : ∀ b,
      ‖(A_coarse (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ ε)
    (hΓ1 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      (Γ_1 b x).length ≤ d * (L - 1))
    (hΓ2 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      (Γ_2 b x).length ≤ d * (L - 1))
    (hΓ3 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      (Γ_3 b x).length ≤ d * (L - 1))
    (b : PhysicalBond d N') : SUN Nc := by
  let C := positiveEdgeOfPhysicalBond b
  let S := blockOf L N' (FiniteLatticeGeometry.src
    (d := d) (N := N') (G := SUN Nc) C)
  let B := cmp99UbarPhysicalNoWindingBudget d L Nc ε hsmall
  let D : FinBox d (L * N') → SUN Nc := fun x =>
    UbarDeviation A_fine A_coarse C x (Γ_1 b) (Γ_2 b) (Γ_3 b)
  exact cmp99UbarSpecialUnitaryBlockOfDeviationBudget
    S (fun _ => (L ^ d : ℝ)⁻¹) D B (by
      intro x hx
      have hlog := norm_UbarDeviationLogArg_le_physicalNoWindingBudget
        A_fine A_coarse C x (Γ_1 b) (Γ_2 b) (Γ_3 b)
        ε hε hsmall (hfine b x hx) (hcoarse b)
        (hΓ1 b x hx) (hΓ2 b x hx) (hΓ3 b x hx)
      simpa [D, UbarDeviationLogArg] using hlog)
    (A_coarse C)

/-- The physical Ubar background on the complete oriented coarse lattice.
Negative bonds are reconstructed as inverses of the corresponding positive
values. -/
noncomputable def cmp99PhysicalUbarGaugeConfig
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d L ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ∀ e, (e ∈ Γ_1 b x ∨ e ∈ Γ_2 b x ∨ e ∈ Γ_3 b x) →
        ‖(A_fine e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ ε)
    (hcoarse : ∀ b,
      ‖(A_coarse (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ ε)
    (hΓ1 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      (Γ_1 b x).length ≤ d * (L - 1))
    (hΓ2 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      (Γ_2 b x).length ≤ d * (L - 1))
    (hΓ3 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      (Γ_3 b x).length ≤ d * (L - 1)) :
    GaugeConfig d N' (SUN Nc) :=
  gaugeConfigOfPositiveBonds fun b =>
    cmp99PhysicalUbarBlock A_fine A_coarse Γ_1 Γ_2 Γ_3
      ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3 b

/-! ## Direct deviation-budget interface

This interface is equivalent at the level of the resulting Ubar formula,
but allows source-specific producers to retain sharper constants than a
single common fine/coarse link radius. -/

/-- Construct one physical Ubar block from a direct certified deviation
bound.  No separate fine/coarse radii occur in this interface. -/
noncomputable def cmp99PhysicalUbarBlockOfDeviationBudget
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
          (Γ_1 b) (Γ_2 b) (Γ_3 b)‖ ≤ B.δ)
    (b : PhysicalBond d N') : SUN Nc := by
  let C := positiveEdgeOfPhysicalBond b
  let S := blockOf L N' (FiniteLatticeGeometry.src
    (d := d) (N := N') (G := SUN Nc) C)
  let D : FinBox d (L * N') → SUN Nc := fun x =>
    UbarDeviation A_fine A_coarse C x (Γ_1 b) (Γ_2 b) (Γ_3 b)
  exact cmp99UbarSpecialUnitaryBlockOfDeviationBudget
    S (fun _ => (L ^ d : ℝ)⁻¹) D B (by
      intro x hx
      simpa [D, UbarDeviationLogArg, C] using hdev b x hx)
    (A_coarse C)

/-- Reconstruct the complete oriented coarse configuration from the direct
deviation-budget blocks. -/
noncomputable def cmp99PhysicalUbarGaugeConfigOfDeviationBudget
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
          (Γ_1 b) (Γ_2 b) (Γ_3 b)‖ ≤ B.δ) :
    GaugeConfig d N' (SUN Nc) :=
  gaugeConfigOfPositiveBonds fun b =>
    cmp99PhysicalUbarBlockOfDeviationBudget
      A_fine A_coarse Γ_1 Γ_2 Γ_3 B hdev b

@[simp] theorem cmp99PhysicalUbarGaugeConfigOfDeviationBudget_apply_pos
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (B : MatrixNearLogNoWindingBudget Nc) (hdev)
    (b : PhysicalBond d N') :
    cmp99PhysicalUbarGaugeConfigOfDeviationBudget
        A_fine A_coarse Γ_1 Γ_2 Γ_3 B hdev
        (positiveEdgeOfPhysicalBond b) =
      cmp99PhysicalUbarBlockOfDeviationBudget
        A_fine A_coarse Γ_1 Γ_2 Γ_3 B hdev b := by
  exact gaugeConfigOfPositiveBonds_apply_pos _ b

@[simp] theorem cmp99PhysicalUbarGaugeConfigOfDeviationBudget_apply_neg
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (B : MatrixNearLogNoWindingBudget Nc) (hdev)
    (y : FinBox d N') (mu : Fin d) :
    cmp99PhysicalUbarGaugeConfigOfDeviationBudget
        A_fine A_coarse Γ_1 Γ_2 Γ_3 B hdev (ConcreteEdge.mk y mu false) =
      (cmp99PhysicalUbarBlockOfDeviationBudget
        A_fine A_coarse Γ_1 Γ_2 Γ_3 B hdev (y, mu))⁻¹ := by
  exact gaugeConfigOfPositiveBonds_apply_neg _ y mu

/-- Forgetting the determinant-one certificate recovers the literal matrix
`Ubar` already used by the gauge-covariance theorem. -/
theorem cmp99PhysicalUbarBlock_coe_eq_Ubar
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d L ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine) (hcoarse) (hΓ1) (hΓ2) (hΓ3)
    (b : PhysicalBond d N') :
    (cmp99PhysicalUbarBlock A_fine A_coarse Γ_1 Γ_2 Γ_3
      ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3 b :
        Matrix (Fin Nc) (Fin Nc) ℂ) =
      Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        A_fine A_coarse (positiveEdgeOfPhysicalBond b)
        (Γ_1 b) (Γ_2 b) (Γ_3 b) := by
  change NormedSpace.exp
      (∑ x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b)),
        (L ^ d : ℝ)⁻¹ • nearLog
          (((UbarDeviation A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
            (Γ_1 b) (Γ_2 b) (Γ_3 b) : SUN Nc) :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) *
        (A_coarse (positiveEdgeOfPhysicalBond b) :
          Matrix (Fin Nc) (Fin Nc) ℂ) =
    NormedSpace.exp
      ((L ^ d : ℝ)⁻¹ •
        ∑ x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
            (positiveEdgeOfPhysicalBond b)),
          nearLog
            (((UbarDeviation A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
              (Γ_1 b) (Γ_2 b) (Γ_3 b) : SUN Nc) :
                Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) *
        (A_coarse (positiveEdgeOfPhysicalBond b) :
          Matrix (Fin Nc) (Fin Nc) ℂ)
  apply congrArg (fun Z : Matrix (Fin Nc) (Fin Nc) ℂ =>
    NormedSpace.exp Z *
      (A_coarse (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ))
  exact (Finset.smul_sum
    (r := (L ^ d : ℝ)⁻¹)
    (s := blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)))
    (f := fun x => nearLog
      (((UbarDeviation A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
        (Γ_1 b) (Γ_2 b) (Γ_3 b) : SUN Nc) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1))).symm

@[simp] theorem cmp99PhysicalUbarGaugeConfig_apply_pos
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d L ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine) (hcoarse) (hΓ1) (hΓ2) (hΓ3)
    (b : PhysicalBond d N') :
    cmp99PhysicalUbarGaugeConfig A_fine A_coarse Γ_1 Γ_2 Γ_3
      ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3
      (positiveEdgeOfPhysicalBond b) =
    cmp99PhysicalUbarBlock A_fine A_coarse Γ_1 Γ_2 Γ_3
      ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3 b := by
  exact gaugeConfigOfPositiveBonds_apply_pos _ b

@[simp] theorem cmp99PhysicalUbarGaugeConfig_apply_neg
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d L ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine) (hcoarse) (hΓ1) (hΓ2) (hΓ3)
    (y : FinBox d N') (μ : Fin d) :
    cmp99PhysicalUbarGaugeConfig A_fine A_coarse Γ_1 Γ_2 Γ_3
      ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3
      (ConcreteEdge.mk y μ false) =
    (cmp99PhysicalUbarBlock A_fine A_coarse Γ_1 Γ_2 Γ_3
      ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3 (y, μ))⁻¹ := by
  exact gaugeConfigOfPositiveBonds_apply_neg _ y μ

end

end YangMills.RG
