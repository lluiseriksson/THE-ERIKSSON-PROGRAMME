import YangMills.RG.BalabanCMP99SourceFlowFullPointSourceOwnerBound

/-!
# PRE-VALIDATION: F5 point-source bound in the complete Lie fibre

Source is present; `.olean` has not been materialized and this result is
not compiler-verified. This draft is not a root import or a physical B0.

F3 gives the same complex scalar in every Lie coordinate. The passage to
the Euclidean fibre norm therefore uses exact scalar multiplication, not
a sum of coordinate bounds and not a dimension-dependent norm conversion.
The ordinary outer function norm is not identified with counting PiLp.

This only strengthens the point-source value statement to the complete
complex fibre. Real transport, supported-field action, the regional inverse
dictionary and physical derivatives remain separate F5 obligations.
-/

namespace YangMills.RG
open YangMills
noncomputable section

/-- One scalar acting on every coordinate gives an exact fibre-norm
identity, even when the coordinate type is empty. -/
theorem norm_euclidean_of_common_scalar_draft
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
theorem norm_cmp99SourceFlowFullPointSourceGreen_fibre_le_owner_draft
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
  have hnorm := norm_euclidean_of_common_scalar_draft c v
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

#print axioms norm_euclidean_of_common_scalar_draft
#print axioms norm_cmp99SourceFlowFullPointSourceGreen_fibre_le_owner_draft

end
end YangMills.RG
