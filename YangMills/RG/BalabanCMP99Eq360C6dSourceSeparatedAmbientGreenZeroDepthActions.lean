import YangMills.RG.BalabanCMP99Eq342LeftDerivativeAtTerminalSpacing
import YangMills.RG.BalabanCMP99Eq342RightAdjointAtTerminalSpacing
import YangMills.RG.BalabanCMP99Eq342LaplacianAtTerminalSpacing
import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecayZeroDepth

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Exact depth-zero C6d Green actions at the literal source spacing

The depth-zero full-companion precision uses `spacing` itself in the literal
covariant derivative.  It must not inherit the positive-depth spelling
`ell * spacing`.  These three specializations consume the explicit-terminal-
spacing Eq342 adapters and keep the remaining powers of `ell = L` visible in
their amplitudes.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]
variable (OmegaSource : ActiveGaugeRegion 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)))
variable (regions : CMP99SourceActiveRegionChain 4 L
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) OmegaSource 0)
variable (hL : 2 ≤ L)
variable {spacing epsilon : ℝ}
variable (background : GaugeConfig 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) (SUN Nc))
variable (chain : CMP99SourceUbarRadiusChain 4 L Nc 0 epsilon)
variable (fineSmall : ∀ e : ConcreteEdge 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)),
  ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)

/-- The literal depth-zero left derivative uses terminal spacing `spacing`,
not `L * spacing`. -/
theorem
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_leftDerivative_blockLocalizedSupBound
    (hspacing : 0 < spacing)
    {decay : ℝ} (hdecay : 0 < decay)
    (root : ActiveGaugeRegion.Site OmegaSource) :
    letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
    let ell := L ^ (0 + 1)
    let A :=
      cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
        (Nc := Nc) regions hL background chain fineSmall decay
    let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
      (Nc := Nc) regions hL background chain fineSmall
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    let ownerRate := (ell : ℝ) * rate
    let ownerAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    let leftAmplitude := ownerAmplitude * (ell : ℝ) *
      ((1 + Real.exp ownerRate) / spacing)
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM OmegaSource
          (matrixSUNAdjointModel Nc) background spacing).comp
        (cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
          (Nc := Nc) regions hL hspacing background chain fineSmall))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      (cmp99Eq342SourceLocalizedBondOwner L K Q 0)
      finBoxDist (leftAmplitude * (ell : ℝ)) ownerRate := by
  dsimp only
  let ell := L ^ (0 + 1)
  let A :=
    cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
      (Nc := Nc) regions hL background chain fineSmall decay
  let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
    (Nc := Nc) regions hL background chain fineSmall
  let rate := finitePiLpExponentialInverseDecayRate A decay
    (cmp99OmegaSiteExpSumBound (decay / 4)) c
  let ownerRate := (ell : ℝ) * rate
  let ownerAmplitude := (2 / c) *
    Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
  let leftAmplitude := ownerAmplitude * (ell : ℝ) *
    ((1 + Real.exp ownerRate) / spacing)
  let G := cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
    (Nc := Nc) regions hL hspacing background chain fineSmall
  letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (0 + 1)
  have hvalue :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      OmegaSource regions hL background chain fineSmall
      hspacing hdecay root
  have hleft :=
    cmp99Eq342_leftDerivative_blockLocalizedSupBound_at_terminalSpacing
      (L := L) (K := K) (Q := Q) (Nc := Nc) (depth := 0)
      OmegaSource background G hspacing hell hvalue
  simpa [G, ell, A, c, rate, ownerRate, ownerAmplitude,
    leftAmplitude] using hleft

/-- The exact depth-zero Green composed with the literal right-adjoint
derivative at terminal spacing `spacing`. -/
theorem
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_rightAdjoint_blockLocalizedSupBound
    (hspacing : 0 < spacing)
    {decay : ℝ} (hdecay : 0 < decay)
    (root : ActiveGaugeRegion.Site OmegaSource) :
    letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
    let ell := L ^ (0 + 1)
    let A :=
      cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
        (Nc := Nc) regions hL background chain fineSmall decay
    let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
      (Nc := Nc) regions hL background chain fineSmall
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    let ownerRate := (ell : ℝ) * rate
    let ownerAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    let rightAmplitude := 648 * ownerAmplitude * Real.exp ownerRate *
      (ell : ℝ) / spacing
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
          (Nc := Nc) regions hL hspacing background chain fineSmall).comp
        (cmp99ActiveRegionSourceCovariantD0CLM OmegaSource
          (matrixSUNAdjointModel Nc) background spacing).adjoint)
      (cmp99Eq342SourceLocalizedBondOwner L K Q 0)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      finBoxDist (rightAmplitude * (ell : ℝ)) ownerRate := by
  dsimp only
  let ell := L ^ (0 + 1)
  let A :=
    cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
      (Nc := Nc) regions hL background chain fineSmall decay
  let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
    (Nc := Nc) regions hL background chain fineSmall
  let rate := finitePiLpExponentialInverseDecayRate A decay
    (cmp99OmegaSiteExpSumBound (decay / 4)) c
  let ownerRate := (ell : ℝ) * rate
  let ownerAmplitude := (2 / c) *
    Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
  let rightAmplitude := 648 * ownerAmplitude * Real.exp ownerRate *
    (ell : ℝ) / spacing
  let G := cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
    (Nc := Nc) regions hL hspacing background chain fineSmall
  letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (0 + 1)
  have hvalue :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      OmegaSource regions hL background chain fineSmall
      hspacing hdecay root
  have hright :=
    cmp99Eq342_rightAdjoint_blockLocalizedSupBound_at_terminalSpacing
      (L := L) (K := K) (Q := Q) (Nc := Nc) (depth := 0)
      OmegaSource background G hspacing hell hvalue
  simpa [G, ell, A, c, rate, ownerRate, ownerAmplitude,
    rightAmplitude] using hright

/-- The literal depth-zero covariant Laplacian action.  The two derivative
factors leave `ell^2 / spacing^2` visible in the amplitude. -/
theorem
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_laplacian_blockLocalizedSupBound
    (hspacing : 0 < spacing)
    {decay : ℝ} (hdecay : 0 < decay)
    (root : ActiveGaugeRegion.Site OmegaSource) :
    letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
    let ell := L ^ (0 + 1)
    let A :=
      cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
        (Nc := Nc) regions hL background chain fineSmall decay
    let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
      (Nc := Nc) regions hL background chain fineSmall
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    let ownerRate := (ell : ℝ) * rate
    let ownerAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    let leftAmplitude := ownerAmplitude * (ell : ℝ) *
      ((1 + Real.exp ownerRate) / spacing)
    let laplacianAmplitude := 4 * leftAmplitude * (ell : ℝ) *
      ((1 + Real.exp ownerRate) / spacing)
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantLaplacian OmegaSource
          (matrixSUNAdjointModel Nc) background spacing).comp
        (cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
          (Nc := Nc) regions hL hspacing background chain fineSmall))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      finBoxDist laplacianAmplitude ownerRate := by
  dsimp only
  let ell := L ^ (0 + 1)
  let A :=
    cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
      (Nc := Nc) regions hL background chain fineSmall decay
  let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
    (Nc := Nc) regions hL background chain fineSmall
  let rate := finitePiLpExponentialInverseDecayRate A decay
    (cmp99OmegaSiteExpSumBound (decay / 4)) c
  let ownerRate := (ell : ℝ) * rate
  let ownerAmplitude := (2 / c) *
    Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
  let leftAmplitude := ownerAmplitude * (ell : ℝ) *
    ((1 + Real.exp ownerRate) / spacing)
  let laplacianAmplitude := 4 * leftAmplitude * (ell : ℝ) *
    ((1 + Real.exp ownerRate) / spacing)
  let G := cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
    (Nc := Nc) regions hL hspacing background chain fineSmall
  letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (0 + 1)
  have hleft :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_leftDerivative_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      OmegaSource regions hL background chain fineSmall
      hspacing hdecay root
  have hlaplacian :=
    cmp99Eq342_laplacian_blockLocalizedSupBound_at_terminalSpacing
      (L := L) (K := K) (Q := Q) (Nc := Nc) (depth := 0)
      OmegaSource background G hspacing hell hleft
  simpa [G, ell, A, c, rate, ownerRate, ownerAmplitude,
    leftAmplitude, laplacianAmplitude] using hlaplacian

end

end YangMills.RG
