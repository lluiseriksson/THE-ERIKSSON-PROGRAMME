import YangMills.RG.BalabanCMP89NeumannScalarReflectionOperator

/-!
# PRE-VALIDATION: mass term through the CMP89 Neumann image series

The source is present, but its `.olean` has not yet been materialized and the
result has not yet been verified by the compiler.

The scalar bare-mass term in the literal three-species precision commutes
exactly with the full multiple-reflection series.  The factor remains the
literal `mass ^ 2`; no decay estimate, image-counting constant or generic
operator bound is introduced.

This is only the mass species of CMP89 (2.42).  It does not prove the
Laplacian reflection identity, the generated `Q′*Q′` reflection identity, the
full-lattice fundamental-solution equation or the complete right-inverse.
-/

namespace YangMills.RG

noncomputable section

variable {d : ℕ}

/-- Multiplying the scalar Neumann series by the bare mass squared is exactly
the Neumann series formed from the mass-multiplied full-space kernel. -/
theorem mass_sq_mul_cmp89NeumannReflectionSeries
    (mass : ℝ)
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (m x n : Fin d → ℤ) :
    mass ^ 2 * cmp89NeumannReflectionSeries fullGreen m x n =
      cmp89NeumannReflectionSeries
        (fun y z => mass ^ 2 * fullGreen y z) m x n := by
  unfold cmp89NeumannReflectionSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [Finset.mul_sum]

variable {ι g : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]

/-- Operator form of the same identity.  The pointwise mass operator acts
after the internally constructed reflection kernel and produces exactly the
reflection operator of the mass-multiplied full-space kernel. -/
theorem mass_sq_comp_cmp89NeumannScalarReflectionOperator
    {m : Fin d → ℤ}
    (mass : ℝ)
    (siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃ ι)
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) :
    ((mass ^ 2) • ContinuousLinearMap.id ℝ (FinitePiLpField ι g)).comp
        (cmp89NeumannScalarReflectionOperator
          (g := g) siteEquiv fullGreen) =
      cmp89NeumannScalarReflectionOperator
        (g := g) siteEquiv
        (fun y z => mass ^ 2 * fullGreen y z) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro target
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    cmp89NeumannScalarReflectionOperator,
    finitePiLpScalarKernelOperator]
  change
    mass ^ 2 •
        (∑ source,
          cmp89NeumannScalarReflectionKernel siteEquiv fullGreen
              target source • f source) =
      ∑ source,
        cmp89NeumannScalarReflectionKernel siteEquiv
            (fun y z => mass ^ 2 * fullGreen y z) target source • f source
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro source _
  rw [smul_smul]
  congr 1
  unfold cmp89NeumannScalarReflectionKernel
  exact mass_sq_mul_cmp89NeumannReflectionSeries mass fullGreen _ _ _

end

end YangMills.RG
