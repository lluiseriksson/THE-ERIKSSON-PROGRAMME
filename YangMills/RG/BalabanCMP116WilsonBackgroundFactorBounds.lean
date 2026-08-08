import YangMills.RG.BalabanCMP116WilsonOrientedEdgeVariation
import YangMills.RG.BalabanCMP116FourFactorLipschitz

/-!
# Uniform bounds for oriented Wilson background factors

This module turns the physical small-background condition on positive bonds
into the orientation-independent estimates needed by the heterogeneous
four-factor telescoping bound.

No Hessian or kernel estimate is assumed here.  Unitarity gives norm exactly
one, while the reverse orientation preserves the distance to the identity by
conjugate transpose.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The background matrix carried by an oriented physical edge. -/
def orientedWilsonBackgroundFactor
    (U : PhysicalGaugeBackground d N Nc) (e : ConcreteEdge d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  if e.sign then
    orientedWilsonPositiveBase U e
  else
    (orientedWilsonPositiveBase U e)ᴴ

/-- Operator-norm smallness of the physical background on positive bonds. -/
def PhysicalWilsonSmallBackground
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ) : Prop :=
  ∀ b : PhysicalBond d N,
    ‖(U (positiveEdgeOfPhysicalBond b)).val - 1‖ ≤ ε

/-- Every positive background link has operator norm one. -/
theorem norm_orientedWilsonPositiveBase
    (U : PhysicalGaugeBackground d N Nc) (e : ConcreteEdge d N) :
    ‖orientedWilsonPositiveBase U e‖ = 1 := by
  classical
  let M := orientedWilsonPositiveBase U e
  have hunitary :
      M ∈ Matrix.unitaryGroup (Fin Nc) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp
      (U (positiveEdgeOfPhysicalBond
        (physicalBondOfEdge e))).property).1
  have hmul : Mᴴ * M = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hunitary)
  have hone :
      ‖(1 : Matrix (Fin Nc) (Fin Nc) ℂ)‖ = 1 := by
    rw [show (1 : Matrix (Fin Nc) (Fin Nc) ℂ) =
        Matrix.diagonal (fun _ => 1) by ext i j; simp]
    rw [Matrix.l2_opNorm_diagonal]
    simp
  have hsq : ‖M‖ * ‖M‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hmul]
    exact hone
  have hnonneg : 0 ≤ ‖M‖ := norm_nonneg M
  nlinarith

/-- Every oriented background factor, including a reversed link, has norm one. -/
theorem norm_orientedWilsonBackgroundFactor
    (U : PhysicalGaugeBackground d N Nc) (e : ConcreteEdge d N) :
    ‖orientedWilsonBackgroundFactor U e‖ = 1 := by
  cases h : e.sign
  · simp only [orientedWilsonBackgroundFactor, h, Bool.false_eq_true, if_false,
      Matrix.l2_opNorm_conjTranspose, norm_orientedWilsonPositiveBase]
  · simp only [orientedWilsonBackgroundFactor, h, if_true,
      norm_orientedWilsonPositiveBase]

/-- The oriented factor of the trivial physical background is the identity. -/
theorem orientedWilsonBackgroundFactor_trivial
    (e : ConcreteEdge d N) :
    orientedWilsonBackgroundFactor
        (trivialPhysicalGaugeBackground d N Nc) e = 1 := by
  cases h : e.sign
  · simp [orientedWilsonBackgroundFactor, h, orientedWilsonPositiveBase,
      trivialPhysicalGaugeBackground]
  · simp [orientedWilsonBackgroundFactor, h, orientedWilsonPositiveBase,
      trivialPhysicalGaugeBackground]

/-- Smallness on positive bonds propagates to both edge orientations with no
loss in the constant. -/
theorem norm_orientedWilsonBackgroundFactor_sub_trivial_le
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (e : ConcreteEdge d N) :
    ‖orientedWilsonBackgroundFactor U e -
        orientedWilsonBackgroundFactor
          (trivialPhysicalGaugeBackground d N Nc) e‖ ≤ ε := by
  rw [orientedWilsonBackgroundFactor_trivial]
  cases h : e.sign
  · simp only [orientedWilsonBackgroundFactor, h, Bool.false_eq_true, if_false]
    calc
      ‖(orientedWilsonPositiveBase U e)ᴴ - 1‖
          = ‖(orientedWilsonPositiveBase U e - 1)ᴴ‖ := by
              simp
      _ = ‖orientedWilsonPositiveBase U e - 1‖ :=
        Matrix.l2_opNorm_conjTranspose _
      _ ≤ ε := hsmall (physicalBondOfEdge e)
  · simp only [orientedWilsonBackgroundFactor, h, if_true]
    exact hsmall (physicalBondOfEdge e)

end

end YangMills.RG
