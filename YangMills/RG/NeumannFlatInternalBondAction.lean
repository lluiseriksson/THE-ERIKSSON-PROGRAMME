import YangMills.RG.NeumannInternalBondStencil
import YangMills.RG.BalabanCMP99SourceFlatPhysicalTransport

/-!
# PRE-VALIDATION: NeumannFlatInternalBondAction, exact HOT-body promotion

Source present; production .olean not materialized; production result not
compiler-verified. The draft passed the bounded HOT gate at 69a5308c8e5635b95b59c6d5c88d4b5b789f851c.
This promotion retains its mathematical body; a fresh cold gate is required.
Scope: actual torus internal bonds only. No integer boundary identification,
regional Green inverse, uniform physical B0 or window15 attainment is claimed.
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
  simp only [neumannFlatInternalBond_extendedDerivative_apply, FinBox.shift_shiftBack]
  simp only [cmp99SourceFlatGaugeConfig, inv_one, SUNAdjointModel.ad_one_apply]


end
end YangMills.RG
