import YangMills.RG.BalabanCMP99SourceFlowFullPointSourceOwnerBound

/-!
# PRE-VALIDATION: Literal source-flow point-source Green bound in the complete Lie fibre

Source present; this promoted module's .olean is not yet materialized and
its promoted result is not yet compiler-verified. The corresponding draft
passed the bounded F5 hot diagnostics recorded in ledger Addendum 1117;
that diagnostic is not a cold seal of this module.

The sealed F3 equality gives one common scalar on the entire Lie fibre,
so the norm bound pays no Nc^2-1 factor. This is a point-source value bound,
not the regional inverse dictionary or the three derivative estimates.
No window-15 attainment or terminal obligation is claimed.
-/

namespace YangMills.RG
open YangMills
noncomputable section

/-- One scalar acting on every coordinate gives an exact fibre-norm
identity, even when the coordinate type is empty. -/
theorem norm_euclidean_of_common_scalar
    {ι : Type*} [Fintype ι] (c : ℂ)
    (v w : EuclideanSpace ℂ ι)
    (h : ∀ i, w i = c * v i) :
    ‖w‖ = ‖c‖ * ‖v‖ := by
  have heq : w = c • v := by
    apply PiLp.ext
    intro i
    exact h i
  rw [heq, norm_smul]

variable {L Kloc Q Nc : ℕ}
variable [NeZero L] [NeZero Kloc] [NeZero Q] [NeZero Nc]

/-- The cold F3 coordinate identity implies its full complex-fibre value
bound with precisely the same amplitude and owner distance. No factor
`Nc^2-1`, owner cardinality, or outer-norm equivalence is used. -/
theorem norm_cmp99SourceFlowFullPointSourceGreen_fibre_le_owner
    (hL : 2 ≤ L) (depth : ℕ) {a rho : ℝ} (ha : 0 < a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (source target : FinBox 4 (L ^ (depth + 1) * (2 * (Kloc * Q))))
    (v : SUNLieComplexCoord Nc) :
    ‖cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
        (L := L) (K := Kloc) (Q := Q) (Nc := Nc) hL depth ha
        (cmp99FlatComplexFibrePointSource source v) target‖ ≤
      (cmp99PhysicalFullGreenOwnerAmplitude (L ^ (depth + 1))
        (cmp99SourceFlowFlatFullComplexA a L depth) rho *
        Real.exp (-rho * (finBoxDist
          (blockSite (L ^ (depth + 1)) (2 * (Kloc * Q)) source)
          (blockSite (L ^ (depth + 1)) (2 * (Kloc * Q)) target) : ℝ))) * ‖v‖ := by
  let c : ℂ := (((((L ^ (depth + 1) : ℕ) : ℂ) ^ 4)⁻¹) *
    cmp99PhysicalFullGreenUnscaledOwnerResidueSum
      (K := L ^ (depth + 1)) (N := 2 * (Kloc * Q))
      (cmp99SourceFlowFlatFullComplexA a L depth) source target)
  have hnorm := norm_euclidean_of_common_scalar c v
    (cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
      (L := L) (K := Kloc) (Q := Q) (Nc := Nc) hL depth ha
      (cmp99FlatComplexFibrePointSource source v) target)
    (fun A => cmp99SourceFlowFullPointSourceGreen_apply_eq_scaledOwnerResidue
      (L := L) (Kloc := Kloc) (Q := Q) (Nc := Nc)
      hL depth ha hrho hamplitude hradius hdenWindow hpairWindow
      source target v A)
  rw [hnorm]
  have hcoeff : 0 < cmp99SourceFlowFlatFullComplexA a L depth := by
    simpa [cmp99SourceFlowFlatFullComplexA] using
      (cmp99SourceMassParameter_pos ha (by exact_mod_cast (NeZero.pos L)) depth)
  have hc := norm_cmp99PhysicalFullGreenScaledOwnerResidue_le_owner
    (R := L ^ (depth + 1)) (N := 2 * (Kloc * Q))
    hcoeff.le hrho hamplitude hradius hdenWindow hpairWindow source target
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg v)


end
end YangMills.RG

