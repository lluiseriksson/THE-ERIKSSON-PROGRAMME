import NeumannPhysicalBoundaryTransferDraft
import NeumannBoundaryImageSeriesReindexDraft
import YangMills.RG.NeumannActualFullGreenReflectionSummability

/-!
# PRE-VALIDATION: actual two-endpoint source-image boundary invariant
Source present; .olean not materialized; result not compiler-verified.
This combines physical endpoint transfer with fixed-source reindexing.
The fine/block boundary equality is explicit. Summability is constructed
from the existing actual full Green bound with all source windows retained.
Only all-reflecting image families are covered; mixed FULL torus directions,
the regional point-source equation and inverse identification remain open.
-/

namespace YangMills.RG
noncomputable section

theorem neumannActualFullGreenImage_summable_boundaryInvariant
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (c B : ℤ) (m target source : Fin 4 → ℤ)
    (hm : ∀ i, 0 < m i)
    (hboundary : c * m mu = ((L ^ j : ℕ) : ℤ) * B) :
    Summable (fun k : Fin 4 → ℤ => ∑ b : Fin 4 → Bool,
      cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
        (cmp89NeumannReflectionImage m source k b)) ∧
    cmp89NeumannReflectionSeries
      (cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a) m
      (fun i => if i = mu then 2*c*m mu-1-target i else target i) source =
    cmp89NeumannReflectionSeries
      (cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a) m target source := by
  refine ⟨summable_neumannActualFullGreenReflection_sum
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass hm, ?_⟩
  have hphase : 2 * ((L ^ j : ℕ) : ℤ) * B = 2*c*m mu := by
    calc
      2 * ((L ^ j : ℕ) : ℤ) * B = 2 * (((L ^ j : ℕ) : ℤ) * B) := by ring
      _ = 2 * (c * m mu) := by rw [hboundary]
      _ = 2*c*m mu := by ring
  have hterm : ∀ (k : Fin 4 → ℤ) (b : Fin 4 → Bool),
      cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
        (fun i => if i = mu then 2*c*m mu-1-target i else target i)
        (cmp89NeumannReflectionImage m source k b) =
      cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
        (fun i => if i = mu then
          2*c*m mu-1-cmp89NeumannReflectionImage m source k b i
          else cmp89NeumannReflectionImage m source k b i) := by
    intro k b
    simpa only [hphase] using
      neumannPhysicalGreen_blockBoundaryTransfer_massUniform
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass
        mu B target (cmp89NeumannReflectionImage m source k b)
  unfold cmp89NeumannReflectionSeries
  simp_rw [hterm]
  exact neumannBoundaryImage_reflected_source_sum mu c m source
    (cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target)

end
end YangMills.RG

#print axioms YangMills.RG.neumannActualFullGreenImage_summable_boundaryInvariant
