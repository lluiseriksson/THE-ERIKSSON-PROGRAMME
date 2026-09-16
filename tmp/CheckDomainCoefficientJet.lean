import YangMills.RG.BalabanCMP102Eq80CorrectedRectangularSourceJetBound
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainCoefficientRegularity
import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivativeBound

#check YangMills.RG.iteratedFDeriv_propagatorSlice_eq_partialPropagatorJet
#check YangMills.RG.cmp102PartialPropagatorJetFieldDerivative_hasFDerivAt
#check YangMills.RG.norm_cmp102PartialPropagatorJetSecondFieldDerivative_le
#check YangMills.RG.hasDerivAt_cmp102Eq80GlobalPotential_affinePropagator
#check iteratedFDeriv_one_apply
#check norm_iteratedFDeriv_one
#check HasFDerivAt.fderiv
#check HasDerivAt.deriv
#check HasFDerivAt.clm_apply
#check ContDiff.contDiff_iteratedFDeriv
#check ContDiff.differentiable_iteratedFDeriv

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

theorem test_directional_eq_partial
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (H K : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J A : E)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    cmp102Eq80PropagatorDirectionalDerivative D D₃ H K Δπ J A
        (fderiv ℝ V₀ (A - H (D A))) =
      cmp102PartialPropagatorJet
        (fun p : (F →L[ℝ] E) × E =>
          cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
        1 H (fun _ => K) A := by
  let Φ : (F →L[ℝ] E) × E → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  have hΦ : ContDiff ℝ ⊤ Φ :=
    contDiff_cmp102Eq80JointPotential_rectangular
      D D₃ V₀ Δπ J hD hD₃ hV₀
  rw [← iteratedFDeriv_propagatorSlice_eq_partialPropagatorJet
    Φ hΦ 1 H (fun _ => K) A]
  rw [iteratedFDeriv_one_apply]
  have hline :=
    hasDerivAt_cmp102Eq80GlobalPotential_affinePropagator
      D D₃ V₀ H K Δπ J A 0
      (fderiv ℝ V₀ (A - H (D A)))
      (by
        simpa using
          (hV₀.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have hpath : HasDerivAt (fun u : ℝ => H + u • K) K 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) H).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const K) using 1 <;>
      simp
  have hslice : ContDiff ℝ ⊤ (fun L : F →L[ℝ] E => Φ (L, A)) :=
    hΦ.comp (contDiff_id.prodMk contDiff_const)
  have hlineRaw :=
    (((hslice.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
      0 hpath).hasDerivAt)
  have hline' : HasDerivAt
      (fun u : ℝ => Φ (H + u • K, A))
      (fderiv ℝ (fun L : F →L[ℝ] E => Φ (L, A)) H K) 0 := by
    simpa [Function.comp_def] using hlineRaw
  simpa [Φ] using hline.unique hline'

end

end YangMills.RG
