/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalUbarGaugeConfig

/-!
# Gauge covariance of the physical CMP99 Ubar background

The abstract matrix-valued covariance theorem for `Ubar` is consumed here by
the literal special-unitary block constructed from the CMP99 physical
small-field budget.  The smallness certificate for the original background is
used to justify the principal logarithm.  Separate small-field certificates
for the gauge-transformed input are required only to construct the transformed
physical block; no false claim that linkwise distance from the identity is
preserved by an arbitrary local gauge transformation is made.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {d N' L Nc : ℕ} [NeZero d] [NeZero N'] [NeZero L] [NeZero Nc]

local notation "FineEdge" =>
  FiniteLatticeGeometry.E (d := d) (N := L * N') (G := SUN Nc)

local instance matrixRationalNormedAlgebraForPhysicalUbarCovariance :
    NormedAlgebra ℚ (Matrix (Fin Nc) (Fin Nc) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

/-- A physical positive Ubar block transforms by the fine gauge values at the
two coarse block basepoints. -/
theorem cmp99PhysicalUbarBlock_gaugeAct
    (u : GaugeTransform d (L * N') (SUN Nc))
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d L ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine) (hcoarse) (hfineT) (hcoarseT)
    (hΓ1) (hΓ2) (hΓ3)
    (hpath1 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      IsPathFrom
        (blockBasepoint L N' (FiniteLatticeGeometry.src (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b)))
        (Γ_1 b x))
    (hend1 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      pathEnd
        (blockBasepoint L N' (FiniteLatticeGeometry.src (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b)))
        (Γ_1 b x) = x)
    (hpath2 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      IsPathFrom x (Γ_2 b x))
    (hpath3 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      IsPathFrom (pathEnd x (Γ_2 b x)) (Γ_3 b x))
    (hend3 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      pathEnd (pathEnd x (Γ_2 b x)) (Γ_3 b x) =
        blockBasepoint L N' (FiniteLatticeGeometry.dst (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b)))
    (b : PhysicalBond d N') :
    cmp99PhysicalUbarBlock
        (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
        Γ_1 Γ_2 Γ_3 ε hε hsmall hfineT hcoarseT hΓ1 hΓ2 hΓ3 b =
      coarseTransform u (FiniteLatticeGeometry.src (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b)) *
        cmp99PhysicalUbarBlock A_fine A_coarse Γ_1 Γ_2 Γ_3
          ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3 b *
        (coarseTransform u (FiniteLatticeGeometry.dst (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b)))⁻¹ := by
  let C := positiveEdgeOfPhysicalBond b
  have hY : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc) C),
      ‖UbarDeviationLogArg (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        A_fine A_coarse C x (Γ_1 b) (Γ_2 b) (Γ_3 b)‖ < 1 := by
    intro x hx
    exact lt_of_le_of_lt
      (norm_UbarDeviationLogArg_le_physicalNoWindingBudget
        A_fine A_coarse C x (Γ_1 b) (Γ_2 b) (Γ_3 b)
        ε hε hsmall (hfine b x hx) (hcoarse b)
        (hΓ1 b x hx) (hΓ2 b x hx) (hΓ3 b x hx))
      (cmp99UbarPhysicalNoWindingBudget d L Nc ε hsmall).δ_lt_one
  apply Subtype.ext
  rw [cmp99PhysicalUbarBlock_coe_eq_Ubar]
  calc
    Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
        C (Γ_1 b) (Γ_2 b) (Γ_3 b) =
      (MatrixRealization.rep
          (u (blockBasepoint L N' (FiniteLatticeGeometry.src C))) :
          (Matrix (Fin Nc) (Fin Nc) ℂ)ˣ).val *
        Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          A_fine A_coarse C (Γ_1 b) (Γ_2 b) (Γ_3 b) *
        (MatrixRealization.rep
          (u (blockBasepoint L N' (FiniteLatticeGeometry.dst C))) :
          (Matrix (Fin Nc) (Fin Nc) ℂ)ˣ)⁻¹.val :=
      Ubar_gaugeAct (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        u A_fine A_coarse C (Γ_1 b) (Γ_2 b) (Γ_3 b)
        (hpath1 b) (hend1 b) (hpath2 b) (hpath3 b) (hend3 b) hY
    _ = (MatrixRealization.rep
        (coarseTransform u (FiniteLatticeGeometry.src C) *
          cmp99PhysicalUbarBlock A_fine A_coarse Γ_1 Γ_2 Γ_3
            ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3 b *
          (coarseTransform u (FiniteLatticeGeometry.dst C))⁻¹) :
          (Matrix (Fin Nc) (Fin Nc) ℂ)ˣ).val := by
      simp only [map_mul, map_inv, Units.val_mul, matrixRealizationSUN_val]
      rw [cmp99PhysicalUbarBlock_coe_eq_Ubar]
      rfl
    _ = (coarseTransform u (FiniteLatticeGeometry.src C) *
        cmp99PhysicalUbarBlock A_fine A_coarse Γ_1 Γ_2 Γ_3
          ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3 b *
        (coarseTransform u (FiniteLatticeGeometry.dst C))⁻¹ : SUN Nc) :=
      matrixRealizationSUN_val _

/-- The complete oriented physical Ubar background is gauge covariant.  The
negative-edge case is forced by the orientation law of `GaugeConfig`, not by
an independent calculation. -/
theorem cmp99PhysicalUbarGaugeConfig_gaugeAct
    (u : GaugeTransform d (L * N') (SUN Nc))
    (A_fine : GaugeConfig d (L * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (L * N') → List FineEdge)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d L ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine) (hcoarse) (hfineT) (hcoarseT)
    (hΓ1) (hΓ2) (hΓ3)
    (hpath1 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      IsPathFrom
        (blockBasepoint L N' (FiniteLatticeGeometry.src (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b)))
        (Γ_1 b x))
    (hend1 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      pathEnd
        (blockBasepoint L N' (FiniteLatticeGeometry.src (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b)))
        (Γ_1 b x) = x)
    (hpath2 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      IsPathFrom x (Γ_2 b x))
    (hpath3 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      IsPathFrom (pathEnd x (Γ_2 b x)) (Γ_3 b x))
    (hend3 : ∀ b x,
      x ∈ blockOf L N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      pathEnd (pathEnd x (Γ_2 b x)) (Γ_3 b x) =
        blockBasepoint L N' (FiniteLatticeGeometry.dst (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b))) :
    cmp99PhysicalUbarGaugeConfig
        (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
        Γ_1 Γ_2 Γ_3 ε hε hsmall hfineT hcoarseT hΓ1 hΓ2 hΓ3 =
      gaugeAct (coarseTransform u)
        (cmp99PhysicalUbarGaugeConfig A_fine A_coarse Γ_1 Γ_2 Γ_3
          ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3) := by
  let AbarT := cmp99PhysicalUbarGaugeConfig
    (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
    Γ_1 Γ_2 Γ_3 ε hε hsmall hfineT hcoarseT hΓ1 hΓ2 hΓ3
  let Abar := cmp99PhysicalUbarGaugeConfig A_fine A_coarse Γ_1 Γ_2 Γ_3
    ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3
  have hpos (b : PhysicalBond d N') :
      AbarT (positiveEdgeOfPhysicalBond b) =
        gaugeAct (coarseTransform u) Abar (positiveEdgeOfPhysicalBond b) := by
    dsimp [AbarT, Abar]
    rw [cmp99PhysicalUbarGaugeConfig_apply_pos]
    change
      cmp99PhysicalUbarBlock
          (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
          Γ_1 Γ_2 Γ_3 ε hε hsmall hfineT hcoarseT hΓ1 hΓ2 hΓ3 b =
        coarseTransform u (FiniteLatticeGeometry.src (G := SUN Nc)
            (positiveEdgeOfPhysicalBond b)) *
          cmp99PhysicalUbarBlock A_fine A_coarse Γ_1 Γ_2 Γ_3
            ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3 b *
          (coarseTransform u (FiniteLatticeGeometry.dst (G := SUN Nc)
            (positiveEdgeOfPhysicalBond b)))⁻¹
    exact cmp99PhysicalUbarBlock_gaugeAct u A_fine A_coarse Γ_1 Γ_2 Γ_3
      ε hε hsmall hfine hcoarse hfineT hcoarseT hΓ1 hΓ2 hΓ3
      hpath1 hend1 hpath2 hpath3 hend3 b
  change AbarT = gaugeAct (coarseTransform u) Abar
  apply gaugeConfig_ext
  intro e
  rcases e with ⟨y, μ, sign⟩
  cases sign with
  | true =>
      exact hpos (y, μ)
  | false =>
      let epos := positiveEdgeOfPhysicalBond (y, μ)
      calc
        AbarT (ConcreteEdge.mk y μ false) = (AbarT epos)⁻¹ := by
          simpa [epos, positiveEdgeOfPhysicalBond] using AbarT.map_reverse epos
        _ = (gaugeAct (coarseTransform u) Abar epos)⁻¹ :=
          congrArg Inv.inv (hpos (y, μ))
        _ = gaugeAct (coarseTransform u) Abar
            (ConcreteEdge.mk y μ false) := by
          simpa [epos, positiveEdgeOfPhysicalBond] using
            (gaugeAct (coarseTransform u) Abar).map_reverse epos |>.symm

end

end YangMills.RG
