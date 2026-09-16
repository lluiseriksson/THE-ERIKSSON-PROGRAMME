/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

H5e3b: extend H5e3a from one generated point source to an arbitrary coarse
field supported in one identity-owner fibre.  The existing exact reduction to
the point source is consumed; no owner-fibre or fine-site cardinality enters.
Regional B0, window-15 attainment and terminal fields remain open.
-/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderOwnerBound
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Literal generated left derivative acting on an arbitrary coarse field.
The displayed fine-spacing inverse is the derivative normalization, not the
separate Holder factor. -/
def cmp99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldDerivative_draft
    (hL : 2 ≤ L) (depth : ℕ)
    (f : FinitePiLpField (FinBox 4 (2 * (K * Q)))
      (SUNLieComplexCoord Nc))
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (derivMu : Fin 4) : SUNLieComplexCoord Nc :=
  let T :=
    (cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
      (cmp99SourceFlatFullComplexWeightedAdjointCLM
        (d := 4) (M := L ^ (depth + 1))
        (N' := 2 * (K * Q)) (Nc := Nc))
  (cmp89Eq249FineLatticeSpacing (L ^ (depth + 1)) 1 : ℂ)⁻¹ •
    (T (WithLp.ofLp f) (x.shift derivMu) - T (WithLp.ofLp f) x)

/-- H5e3b: the point-source owner estimate extends to one complete
identity-owner fibre with the finite supremum norm and no cardinality loss. -/
theorem
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldHolderDifference_le_owner_draft
    (hL : 2 ≤ L) (depth : ℕ)
    (owner : FinBox 4 (2 * (K * Q)))
    (f : FinitePiLpField (FinBox 4 (2 * (K * Q)))
      (SUNLieComplexCoord Nc))
    (hf : FinitePiLpSupportedInOwner (fun y => y) owner f)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho alpha : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (halphaStrict : alpha < 1) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho)
    (derivMu bondNu : Fin 4) :
    let Kfine := L ^ (depth + 1)
    let N := 2 * (K * Q)
    let a := cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0
    let fineX := cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth x
    let fineY := cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth
      (blockBasepoint Kfine N owner)
    let b : PhysicalBond 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
      (fineX, bondNu)
    let xi := cmp89Eq249FineLatticeSpacing Kfine 1
    let A := cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft
      a rho alpha
    ‖(((xi ^ alpha : ℝ) : ℂ)⁻¹) •
        (cmp99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldDerivative_draft
            (L := L) (K := K) (Q := Q) (Nc := Nc)
            hL depth f x derivMu -
          cmp99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldDerivative_draft
            (L := L) (K := K) (Q := Q) (Nc := Nc)
            hL depth f (x.shift bondNu) derivMu)‖ ≤
      (A *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          (Real.exp ((rho * xi) *
              (2 * (L ^ (depth + 1) - 1) : ℕ)) *
            Real.exp (-rho *
              (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
                depth b fineY : ℝ)))) * finitePiLpSupNorm f) := by
  dsimp only
  let Kfine : ℕ := L ^ (depth + 1)
  let N : ℕ := 2 * (K * Q)
  let a : ℝ := cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
    (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0
  let fineX := cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth x
  let fineY := cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth
    (blockBasepoint Kfine N owner)
  let b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
    (fineX, bondNu)
  let xi := cmp89Eq249FineLatticeSpacing Kfine 1
  let A := cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft
    a rho alpha
  let C : ℝ := A *
    ((2 / (1 - Real.exp (-rho))) ^ 4 *
      (Real.exp ((rho * xi) *
          (2 * (L ^ (depth + 1) - 1) : ℕ)) *
        Real.exp (-rho *
          (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
            depth b fineY : ℝ))))
  have hfpoint :=
    finitePiLp_of_supportedInIdentityOwner_eq_flatComplexFibrePointSource
      owner f hf
  have hpoint :=
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderDifference_le_owner_draft
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth owner (f owner) x halpha0 halpha1 halphaStrict hrho
      hamplitude hradius hwindow derivMu bondNu
  have hvalue : ‖f owner‖ ≤ finitePiLpSupNorm f :=
    norm_apply_le_finitePiLpSupNorm f owner
  have hden : 0 < 1 - Real.exp (-rho) := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hC : 0 ≤ C := by
    dsimp [C, A, cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft]
    positivity
  unfold cmp99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldDerivative_draft
  rw [hfpoint]
  change ‖(((xi ^ alpha : ℝ) : ℂ)⁻¹) •
      (cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          hL depth owner (f owner) x derivMu -
        cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          hL depth owner (f owner) (x.shift bondNu) derivMu)‖ ≤
    C * finitePiLpSupNorm f
  exact hpoint.trans (mul_le_mul_of_nonneg_left hvalue hC)

end

end YangMills.RG
