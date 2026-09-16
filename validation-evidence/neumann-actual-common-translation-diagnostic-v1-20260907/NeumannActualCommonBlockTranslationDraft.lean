import NeumannActualFullSolutionScalarDraft
import NeumannCommonBlockEndpointPhaseDraft
import YangMills.RG.BalabanCMP89Eq246FinePointSourceHolomorphy

/-!
# PRE-VALIDATION: common block translation of the literal full Green

Source present; .olean not materialized; result not compiler-verified.
Inputs are the actual normalized point-source vector and non-transpose
solution of (2.46). No Green covariance is assumed. The same integer block
shift moves BOTH endpoints; the physical wrapper fixes M=L^j and xi=1/M.
No claim of fine-step translation, reflection, regional inverse, B0 or
window15 is made. Equalities of totalized formulas are not inverse claims
at singular parameters. Diagnostic prerequisite evidence: ledger1183/1185.
-/

namespace YangMills.RG
noncomputable section

theorem neumannActualPointSourceVector_blockShift
    (d L j : ℕ) {M : ℕ} (hM : 0 < M) (z : Fin d → ℂ)
    (source shift : Fin d → ℤ) :
    cmp89Eq246FinePointSourceAliasVector d L j z
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => source mu + (M : ℤ) * shift mu)) =
      fun n => cmp89Eq246FinePointSourceAliasVector d L j z
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) source) n *
        Complex.exp (-Complex.I * ∑ mu, z mu * (shift mu : ℂ)) := by
  funext n
  exact neumannAliasSourcePhase_blockShift hM z n.1 source shift

theorem neumannActualPointSourceSolution_blockShift
    (d L j : ℕ) [NeZero L] {M : ℕ} (hM : 0 < M)
    (mass a : ℝ) (z : Fin d → ℂ) (source shift : Fin d → ℤ)
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246StabilizedFinePointSourceSolution d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => source mu + (M : ℤ) * shift mu)) m =
      cmp89Eq246StabilizedFinePointSourceSolution d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) source) m *
        Complex.exp (-Complex.I * ∑ mu, z mu * (shift mu : ℂ)) := by
  unfold cmp89Eq246StabilizedFinePointSourceSolution
  rw [neumannActualPointSourceVector_blockShift d L j hM]
  exact neumannActualFullSolution_mul_right d L j mass a z _ _ m

theorem neumannActualFineGreenIntegrand_commonBlockShift
    (d L j : ℕ) [NeZero L] {M : ℕ} (hM : 0 < M)
    (mass a : ℝ) (z : Fin d → ℂ) (target source shift : Fin d → ℤ) :
    cmp89Eq246StabilizedFineToFineGreenIntegrand d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => target mu + (M : ℤ) * shift mu))
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => source mu + (M : ℤ) * shift mu)) =
      cmp89Eq246StabilizedFineToFineGreenIntegrand d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) target)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) source) := by
  classical
  unfold cmp89Eq246StabilizedFineToFineGreenIntegrand
  apply Finset.sum_congr rfl
  intro m _
  rw [neumannAliasTargetPhase_blockShift hM,
    neumannActualPointSourceSolution_blockShift d L j hM]
  calc
    _ = (Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m.1)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) target)) *
        cmp89Eq246StabilizedFinePointSourceSolution d L j mass a z
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) source) m) *
        (Complex.exp (Complex.I * ∑ mu, z mu * (shift mu : ℂ)) *
          Complex.exp (-Complex.I * ∑ mu, z mu * (shift mu : ℂ))) := by ring
    _ = _ := by rw [neumannCommonBlockPhase_cancel, mul_one]

theorem neumannActualPhysicalFineGreenIntegrand_commonBlockShift
    (L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin 4 → ℂ)
    (target source shift : Fin 4 → ℤ) :
    cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a z
        (fun mu => target mu + ((L ^ j : ℕ) : ℤ) * shift mu)
        (fun mu => source mu + ((L ^ j : ℕ) : ℤ) * shift mu) =
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a z target source := by
  have hM : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  simpa only [cmp89Eq246PhysicalFineToFineGreenIntegrand,
    cmp89Eq249FineLatticeSpacing] using
    neumannActualFineGreenIntegrand_commonBlockShift 4 L j hM mass a z
      target source shift

theorem neumannActualNormalizedFineGreen_commonBlockShift
    (L j : ℕ) [NeZero L] (mass a : ℝ) (target source shift : Fin 4 → ℤ) :
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
        (fun mu => target mu + ((L ^ j : ℕ) : ℤ) * shift mu)
        (fun mu => source mu + ((L ^ j : ℕ) : ℤ) * shift mu) =
      cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target source := by
  unfold cmp89Eq246NormalizedPhysicalFineToFineGreen
  congr 1
  funext x
  exact neumannActualPhysicalFineGreenIntegrand_commonBlockShift L j mass a
    (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ)) target source shift

#print axioms neumannActualPointSourceVector_blockShift
#print axioms neumannActualPointSourceSolution_blockShift
#print axioms neumannActualFineGreenIntegrand_commonBlockShift
#print axioms neumannActualPhysicalFineGreenIntegrand_commonBlockShift
#print axioms neumannActualNormalizedFineGreen_commonBlockShift

end
end YangMills.RG
