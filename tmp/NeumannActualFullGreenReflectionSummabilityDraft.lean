import YangMills.RG.BalabanCMP89NeumannRectangularPhysicalGreenInsertion
import YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenFourierSummability

/-!
PRE-VALIDATION: source present, .olean not materialized, not compiler-verified.

R2 source-image summability for the literal two-endpoint CMP89 (2.46) Green.
Only the GENERIC decay-certificate and image-summability declarations from
the insertion module are reused; its withdrawn (2.48) physical specialization
is not used. No translation-invariance or adjunction premise changes sides.
The amplitude retains L,j,a,rho and the fine rate is rho/(L^j). This is not
uniform physical B0, a regional inverse, or attainment of window15.
-/

namespace YangMills.RG

noncomputable section

/-- Construct the existing image-sum input from the actual full Green bound.
The full kernel is not a supplied family and all strip/mass windows remain. -/
def neumannActualFullGreenDecayCertificate
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass) :
    CMP89FullLatticeGreenDecayCertificate
      (cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a)
      (cmp89Eq246DirectedFullSolutionSumBound L j a rho)
      (rho / ((L ^ j : ℕ) : ℝ)) := by
  have hbound : ∀ x y : Fin 4 → ℤ,
      ‖cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a x y‖ ≤
        cmp89Eq246DirectedFullSolutionSumBound L j a rho *
          cmp89SignedLatticeL1ExponentialWeight
            (rho / ((L ^ j : ℕ) : ℝ)) (x - y) := by
    intro x y
    have h := norm_cmp89Eq246NormalizedPhysicalFineToFineGreen_le_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass x y
    rw [cmp89Eq246PhysicalFineGreenDecay_eq_signedLatticeWeight_massUniform] at h
    simpa only [mul_comm] using h
  refine ⟨?_, ?_, hbound⟩
  · have h := hbound 0 0
    simpa [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs] using
      (le_trans (norm_nonneg _) h)
  · exact div_pos hrho (by
      exact_mod_cast pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)

/-- The printed source-image orientation is absolutely summable for (2.46).
It is not obtained by relabelling an affine-TARGET Fourier coefficient. -/
theorem summable_neumannActualFullGreenReflection_sum
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {m x n : Fin 4 → ℤ} (hm : ∀ mu, 0 < m mu) :
    Summable (fun k : Fin 4 → ℤ =>
      ∑ branch : CMP89NeumannReflectionBranch 4,
        cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a x
          (cmp89NeumannReflectionImage m n k branch)) :=
  summable_cmp89NeumannRectangularFullGreen_sum
    (neumannActualFullGreenDecayCertificate
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass) hm

/-- Real scalar summability for the later real Lie-fibre action, retaining
the literal full two-endpoint kernel rather than its coarse-source factor. -/
theorem summable_neumannActualFullGreenReflection_real_sum
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {m x n : Fin 4 → ℤ} (hm : ∀ mu, 0 < m mu) :
    Summable (fun k : Fin 4 → ℤ =>
      ∑ branch : CMP89NeumannReflectionBranch 4,
        (cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a x
          (cmp89NeumannReflectionImage m n k branch)).re) := by
  have hcomplex := summable_neumannActualFullGreenReflection_sum
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    (x := x) (n := n) ha hrho hamplitude hradius hdenWindow hpairWindow hmass hm
  apply Summable.of_norm_bounded hcomplex.norm
  intro k
  rw [Real.norm_eq_abs, ← Complex.re_sum]
  exact Complex.abs_re_le_norm _

end
end YangMills.RG

#print axioms YangMills.RG.neumannActualFullGreenDecayCertificate
#print axioms YangMills.RG.summable_neumannActualFullGreenReflection_sum
#print axioms YangMills.RG.summable_neumannActualFullGreenReflection_real_sum
