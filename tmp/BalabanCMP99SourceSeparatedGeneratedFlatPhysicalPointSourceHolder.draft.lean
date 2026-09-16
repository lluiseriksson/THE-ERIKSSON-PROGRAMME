/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Exact H5d3 point-source Holder identity.  The generated derivative is
constructed from the literal D4 operator and retains the separate fine-spacing
factor.  No endpoint bound is subtracted, no norm is taken, and no owner,
regional B0, window-15 or terminal claim is made.
-/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalHolderTsum

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Literal internally generated point-source left derivative.  The displayed
fine-spacing inverse is the D4 derivative normalization and is not the Holder
factor. -/
def cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
    (hL : 2 ≤ L) (depth : ℕ)
    (y : FinBox 4 (2 * (K * Q))) (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (derivMu : Fin 4) : SUNLieComplexCoord Nc :=
  let T :=
    (cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
      (cmp99SourceFlatFullComplexWeightedAdjointCLM
        (d := 4) (M := L ^ (depth + 1))
        (N' := 2 * (K * Q)) (Nc := Nc))
  (cmp89Eq249FineLatticeSpacing (L ^ (depth + 1)) 1 : ℂ)⁻¹ •
    (T (cmp99FlatComplexFibrePointSource y v) (x.shift derivMu) -
      T (cmp99FlatComplexFibrePointSource y v) x)

/-- D4 identifies the literal generated derivative with its internally
constructed zero-residue derivative coefficient series. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_eq_series_smul_draft
    (hL : 2 ≤ L) (depth : ℕ)
    (y : FinBox 4 (2 * (K * Q))) (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho)
    (derivMu : Fin 4) :
    let u : Fin 4 → ℤ := fun nu =>
      -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
        (L ^ (depth + 1)) x y nu
    cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        hL depth y v x derivMu =
      (∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          (L ^ (depth + 1)) 1 0
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
          derivMu u n.1) • v := by
  dsimp only
  unfold cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
  simpa using
    (cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_forwardDifference_eq_derivativeSeries_smul_draft
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth y v x hrho hamplitude hradius hwindow derivMu)

/-- The source-minus-target difference of two generated point-source
derivatives, multiplied by the separate physical Holder factor, is exactly the
zero-residue sum of complete Holder integrals acting on the point-source
value.  `derivMu` and `bondNu` remain independent. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderDifference_eq_tsumIntegral_smul_draft
    (hL : 2 ≤ L) (depth : ℕ)
    (y : FinBox 4 (2 * (K * Q))) (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho alpha : ℝ}
    (hrho : 0 < rho)
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
    let u : Fin 4 → ℤ := fun nu =>
      -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement Kfine x y nu
    let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
    let holderU := cmp116CMP89PhysicalBondHolderDisplacement (x, bondNu)
    let xi := cmp89Eq249FineLatticeSpacing Kfine 1
    (((xi ^ alpha : ℝ) : ℂ)⁻¹) •
        (cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
            (L := L) (K := K) (Q := Q) (Nc := Nc)
            hL depth y v x derivMu -
          cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
            (L := L) (K := K) (Q := Q) (Nc := Nc)
            hL depth y v (x.shift bondNu) derivMu) =
      (∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_draft
          Kfine 1 0 a alpha derivMu holderU
          (cmp89SignedLatticeResidueAffineMap Kfine forwardU n.1)) • v := by
  dsimp only
  let Kfine : ℕ := L ^ (depth + 1)
  let N : ℕ := 2 * (K * Q)
  let a : ℝ := cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
    (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0
  let u : Fin 4 → ℤ := fun nu =>
    -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement Kfine x y nu
  let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
  let holderU := cmp116CMP89PhysicalBondHolderDisplacement (x, bondNu)
  let xi := cmp89Eq249FineLatticeSpacing Kfine 1
  let c : ℂ := (((xi ^ alpha : ℝ) : ℂ)⁻¹)
  let sourceSeries : ℂ :=
    ∑' n : CMP99FlatIntegerResidueClass 4 N 0,
      cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
        Kfine 1 0 a derivMu u n.1
  let targetSeries : ℂ :=
    ∑' n : CMP99FlatIntegerResidueClass 4 N 0,
      cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
        Kfine 1 0 a derivMu
        (fun nu =>
          -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
            Kfine (x.shift bondNu) y nu) n.1
  let forwardSeries : ℂ :=
    ∑' n : CMP99FlatIntegerResidueClass 4 N 0,
      cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
        Kfine 1 0 a derivMu forwardU n.1
  have hsource :=
    cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_eq_series_smul_draft
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth y v x hrho hamplitude hradius hwindow derivMu
  have htarget :=
    cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_eq_series_smul_draft
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth y v (x.shift bondNu) hrho hamplitude hradius hwindow derivMu
  have hreindex :=
    tsum_cmp99SourceSeparatedGeneratedFlatPhysicalDerivative_shift_eq_forward_draft
      (K := Kfine) (N := N) x y derivMu bondNu 0 a
  have hintegral :=
    tsum_cmp89Eq249PhysicalHolderIntegral_eq_xiRpowInv_mul_derivativeDiff_draft
      (K := Kfine) (N := N) (mass := 0) (a := a)
      (alpha := alpha) (rho := rho)
      (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
      hrho hamplitude hradius hwindow (by norm_num)
      x derivMu bondNu u
  change c •
      (cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          hL depth y v x derivMu -
        cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          hL depth y v (x.shift bondNu) derivMu) = _
  change _ =
    (∑' n : CMP99FlatIntegerResidueClass 4 N 0,
      cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_draft
        Kfine 1 0 a alpha derivMu holderU
        (cmp89SignedLatticeResidueAffineMap Kfine forwardU n.1)) • v
  change
    cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        hL depth y v x derivMu = sourceSeries • v at hsource
  change
    cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        hL depth y v (x.shift bondNu) derivMu = targetSeries • v at htarget
  change targetSeries = forwardSeries at hreindex
  change
    (∑' n : CMP99FlatIntegerResidueClass 4 N 0,
      cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_draft
        Kfine 1 0 a alpha derivMu holderU
        (cmp89SignedLatticeResidueAffineMap Kfine forwardU n.1)) =
      c * (sourceSeries - forwardSeries) at hintegral
  rw [hsource, htarget, hreindex, hintegral]
  simp only [smul_sub, smul_smul, mul_sub, sub_smul]

end

end YangMills.RG
