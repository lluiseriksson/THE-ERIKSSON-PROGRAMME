import YangMills.RG.FinitePiLpCanonicalComplexificationOuterTransport

/-!
# PRE-VALIDATION: exact real-slice transport at a single output fibre

Source is present; `.olean` has not been materialized and these results
are not compiler-verified. No root import is added.

The real-to-complex Euclidean inclusion preserves the fibre norm. The
outer continuous equivalence is used only to transport coordinates and
operator application; it is NOT asserted to preserve the outer norm.
These generic statements do not identify any regional Green operator.
-/

namespace YangMills.RG
open YangMills
noncomputable section

/-- The physical Lie-coordinate inclusion preserves the complete fibre
norm, including the zero-dimensional case. -/
theorem norm_cmp99SUNLieCoordComplexificationLM_draft
    {Nc : ℕ} (v : SUNLieCoord Nc) :
    ‖cmp99SUNLieCoordComplexificationLM Nc v‖ = ‖v‖ := by
  simp only [PiLp.norm_eq_of_L2,
    cmp99SUNLieCoordComplexificationLM_apply, Complex.norm_real]

/-- The same norm identity for any finite real Euclidean coordinate set;
this is only a fibre norm, never a change of the outer field norm. -/
theorem norm_finitePiLpComplexOfReal_apply_draft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : FinitePiLpField ι (EuclideanSpace ℝ κ)) (i : ι) :
    ‖finitePiLpComplexOfReal x i‖ = ‖x i‖ := by
  simp only [PiLp.norm_eq_of_L2,
    finitePiLpComplexOfReal_apply, Complex.norm_real]

/-- Canonical complexification on the ordinary outer function space
agrees with the real operator after explicit coordinate transport. -/
theorem finitePiLpCanonicalComplexificationOuterCLM_ofReal_draft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ))
    (x : FinitePiLpField ι (EuclideanSpace ℝ κ)) :
    finitePiLpCanonicalComplexificationOuterCLM T
        (finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal x)) =
      finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal (T x)) := by
  change finitePiLpComplexOuterEquiv
      (finitePiLpCanonicalComplexificationCLM T
        (finitePiLpComplexOuterEquiv.symm
          (finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal x)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply,
    finitePiLpCanonicalComplexificationCLM_ofReal]

/-- Evaluating the preceding exact transport at one site preserves the
fibre norm without an outer PiLp/function-space norm comparison. -/
theorem norm_finitePiLpCanonicalComplexificationOuterCLM_ofReal_apply_draft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ))
    (x : FinitePiLpField ι (EuclideanSpace ℝ κ)) (i : ι) :
    ‖finitePiLpCanonicalComplexificationOuterCLM T
        (finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal x)) i‖ =
      ‖T x i‖ := by
  rw [finitePiLpCanonicalComplexificationOuterCLM_ofReal_draft]
  exact norm_finitePiLpComplexOfReal_apply_draft (T x) i

#print axioms norm_cmp99SUNLieCoordComplexificationLM_draft
#print axioms norm_finitePiLpComplexOfReal_apply_draft
#print axioms finitePiLpCanonicalComplexificationOuterCLM_ofReal_draft
#print axioms norm_finitePiLpCanonicalComplexificationOuterCLM_ofReal_apply_draft

end
end YangMills.RG
