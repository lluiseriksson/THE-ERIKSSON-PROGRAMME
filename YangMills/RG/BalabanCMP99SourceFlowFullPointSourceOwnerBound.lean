import YangMills.RG.BalabanCMP99SourceFlowFullPointSourceGreenIdentification
import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceOwnerResidueIdentity
import YangMills.RG.BalabanCMP99GeneratedFullPointSourceOwnerBound

/-!
# PRE-VALIDATION: literal source-flow full point-source owner bound

Source is present; the `.olean` is not materialized and this result is not
verified by the compiler. This source is not imported by the root aggregator.

F3 uses the generic residue identity and F1 inverse uniqueness, not a supplied
Green equality. The generated-owner module contributes only the already
defined scalar amplitude expression: its generated coefficient and coupled
scale specialization are not used. RG ratio L, localization Kloc and period
Q remain independent. R=L^(depth+1) counts fine sites per block; R^-4 is paid
once. The amplitude retains its source coefficient and depth dependence.

No uniform physical B0, derivative/regional bound or window15 is claimed.
Counters remain 20/41 and TermSource=0.
-/

namespace YangMills.RG
open YangMills
noncomputable section

/-- Generic normalized scalar residue: no localization/RG scale coupling. -/
theorem norm_cmp99PhysicalFullGreenScaledOwnerResidue_le_owner
    {R N : ℕ} [NeZero R] [NeZero N] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (source target : FinBox 4 (R * N)) :
    ‖(((R : ℂ) ^ 4)⁻¹) *
      cmp99PhysicalFullGreenUnscaledOwnerResidueSum
        (K := R) (N := N) a source target‖ ≤
      cmp99PhysicalFullGreenOwnerAmplitude R a rho *
        Real.exp (-rho * (finBoxDist
          (blockSite R N source) (blockSite R N target) : ℝ)) := by
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have h := norm_cmp99PhysicalFullGreenUnscaledOwnerResidueSum_le_owner
    (K := R) (N := N) ha hrho hamplitude hradius hdenWindow hpairWindow
    source target
  have hscale : 0 ≤ (((R : ℝ) ^ 4)⁻¹) := by positivity
  simpa only [cmp99PhysicalFullGreenOwnerAmplitude, mul_assoc] using
    (mul_le_mul_of_nonneg_left h hscale)

variable {L Kloc Q Nc : ℕ}
variable [NeZero L] [NeZero Kloc] [NeZero Q] [NeZero Nc]

/-- F2 specialized to the actual source-flow inverse through the named F1
theorem. The endpoints are the literal reflected/swapped residue endpoints. -/
theorem cmp99SourceFlowFullPointSourceGreen_apply_eq_scaledOwnerResidue
    (hL : 2 ≤ L) (depth : ℕ) {a rho : ℝ} (ha : 0 < a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (source target : FinBox 4 (L ^ (depth + 1) * (2 * (Kloc * Q))))
    (v : SUNLieComplexCoord Nc) (A : Fin (Nc ^ 2 - 1)) :
    cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
        (L := L) (K := Kloc) (Q := Q) (Nc := Nc) hL depth ha
        (cmp99FlatComplexFibrePointSource source v) target A =
      (((((L ^ (depth + 1) : ℕ) : ℂ) ^ 4)⁻¹) *
        cmp99PhysicalFullGreenUnscaledOwnerResidueSum
          (K := L ^ (depth + 1)) (N := 2 * (Kloc * Q))
          (cmp99SourceFlowFlatFullComplexA a L depth) source target) * v A := by
  have hcoeff : 0 < cmp99SourceFlowFlatFullComplexA a L depth := by
    simpa [cmp99SourceFlowFlatFullComplexA] using
      (cmp99SourceMassParameter_pos ha (by exact_mod_cast (NeZero.pos L)) depth)
  have hF1 := cmp99SourceFlowFullPointSourceSolution_eq_green_apply
    (L := L) (K := Kloc) (Q := Q) (Nc := Nc) hL depth ha source v
  have hF2 := cmp99SourceFlatFullPointSourceSolution_eq_scaledOwnerResidue
    (Kfine := L ^ (depth + 1)) (N := 2 * (Kloc * Q)) (Nc := Nc)
    hcoeff hrho hamplitude hradius hdenWindow hpairWindow source target v A
  exact (congrArg (fun f :
    FinBox 4 (L ^ (depth + 1) * (2 * (Kloc * Q))) → SUNLieComplexCoord Nc =>
      f target A) hF1).symm.trans hF2

/-- The literal source-flow full Green has an owner bound with all value
costs visible. Uniformity of this amplitude remains the separate F4 gate. -/
theorem norm_cmp99SourceFlowFullPointSourceGreen_le_owner
    (hL : 2 ≤ L) (depth : ℕ) {a rho : ℝ} (ha : 0 < a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (source target : FinBox 4 (L ^ (depth + 1) * (2 * (Kloc * Q))))
    (v : SUNLieComplexCoord Nc) (A : Fin (Nc ^ 2 - 1)) :
    ‖cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
        (L := L) (K := Kloc) (Q := Q) (Nc := Nc) hL depth ha
        (cmp99FlatComplexFibrePointSource source v) target A‖ ≤
      (cmp99PhysicalFullGreenOwnerAmplitude (L ^ (depth + 1))
        (cmp99SourceFlowFlatFullComplexA a L depth) rho *
        Real.exp (-rho * (finBoxDist
          (blockSite (L ^ (depth + 1)) (2 * (Kloc * Q)) source)
          (blockSite (L ^ (depth + 1)) (2 * (Kloc * Q)) target) : ℝ))) * ‖v A‖ := by
  have heq := cmp99SourceFlowFullPointSourceGreen_apply_eq_scaledOwnerResidue
    (L := L) (Kloc := Kloc) (Q := Q) (Nc := Nc)
    hL depth ha hrho hamplitude hradius hdenWindow hpairWindow source target v A
  rw [heq, norm_mul]
  have hcoeff : 0 < cmp99SourceFlowFlatFullComplexA a L depth := by
    simpa [cmp99SourceFlowFlatFullComplexA] using
      (cmp99SourceMassParameter_pos ha (by exact_mod_cast (NeZero.pos L)) depth)
  have h := norm_cmp99PhysicalFullGreenScaledOwnerResidue_le_owner
    (R := L ^ (depth + 1)) (N := 2 * (Kloc * Q))
    hcoeff.le hrho hamplitude hradius hdenWindow hpairWindow source target
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

end
end YangMills.RG
