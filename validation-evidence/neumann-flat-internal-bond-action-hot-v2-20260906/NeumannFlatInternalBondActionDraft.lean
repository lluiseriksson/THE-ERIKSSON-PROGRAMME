import YangMills.RG.NeumannInternalBondStencil
import YangMills.RG.BalabanCMP99SourceFlatPhysicalTransport

/-!
# PRE-VALIDATION: literal flat Neumann internal-bond action

Source present; .olean not materialized; not compiler-verified.
This draft consumes the actual covariant derivative, whose flat sign is
f(source)-f(target). It does not identify it with flatD0FullCLM, which has
the opposite sign. Internal bond masks remain explicit, including torus wraps.
No nonperiodic rectangle boundary law, Green inverse or window15 is claimed.
Compile only after the current production stencil cold gate is preserved.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The actual zero-extended internal derivative is a masked source-minus-
target difference. Both endpoint restrictions are justified by bond membership. -/
theorem neumannFlatInternalBond_extendedDerivative_apply
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (spacing : ℝ) (f : GaugeZeroCochain d N (SUNLieCoord Nc))
    (b : PositiveBond d N) :
    extendZeroOneCLM Omega
        (cmp89SourceNeumannRegionalCovariantD0CLM Omega rho
          (cmp99SourceFlatGaugeConfig d N Nc) spacing
          (restrictZeroCLM Omega f)) b =
      if b ∈ Omega.bonds then
        spacing⁻¹ • (f b.1 - f (b.1.shift b.2)) else 0 := by
  classical
  rcases b with ⟨x, i⟩
  by_cases hb : (x, i) ∈ Omega.bonds
  · have hend : x ∈ Omega.sites ∧ x.shift i ∈ Omega.sites :=
      (Finset.mem_filter.mp hb).2
    simp [extendZeroOneCLM, hb, cmp89SourceNeumannRegionalCovariantD0CLM,
      restrictOneCLM, covariantD0CLM_apply, cmp99SourceFlatGaugeConfig,
      SUNAdjointModel.ad_one_apply, extendZeroZeroCLM, restrictZeroCLM,
      hend.1, hend.2]
  · simp [extendZeroOneCLM, hb]

/-- The finite flat Neumann Laplacian keeps incoming and outgoing bond masks
separate. No site equivalence is used to replace either mask by an integer edge. -/
theorem neumannFlatInternalBond_laplacian_apply
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (spacing : ℝ) (f : GaugeZeroCochain d N (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp89SourceNeumannRegionalLaplacian Omega rho
        (cmp99SourceFlatGaugeConfig d N Nc) spacing
        (restrictZeroCLM Omega f) x =
      spacing⁻¹ • ∑ i : Fin d,
        ((if (x.1, i) ∈ Omega.bonds then
            spacing⁻¹ • (f x.1 - f (x.1.shift i)) else 0) -
          (if (x.1.shiftBack i, i) ∈ Omega.bonds then
            spacing⁻¹ • (f (x.1.shiftBack i) - f x.1) else 0)) := by
  rw [neumannInternalBond_laplacian_apply]
  simp only [neumannFlatInternalBond_extendedDerivative_apply,
    cmp99SourceFlatGaugeConfig, inv_one,
    SUNAdjointModel.ad_one_apply, FinBox.shift_shiftBack]

#print axioms neumannFlatInternalBond_extendedDerivative_apply
#print axioms neumannFlatInternalBond_laplacian_apply

end
end YangMills.RG
