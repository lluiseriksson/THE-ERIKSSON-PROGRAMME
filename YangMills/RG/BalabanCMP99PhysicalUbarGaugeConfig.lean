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
