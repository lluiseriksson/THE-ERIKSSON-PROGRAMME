import YangMills.RG.FinitePiLpCanonicalComplexificationOuterTransport

/-!
# Real-slice norm and operator transport at a single output fibre

Cold-verified and .olean materialized at source 6c49a8da on 2026-09-05.
Downloaded evidence independently verified; see ledger Addendum 1118.
The selective seal changes provenance comments only, not the mathematics.

These generic statements preserve the fibre norm and intertwine canonical
complexification with the real operator. The outer PiLp/function equivalence
transports coordinates; no isometry of outer norms or regional inverse is asserted.
No window-15 attainment or terminal obligation is claimed.
-/

namespace YangMills.RG
open YangMills
noncomputable section

/-- The physical Lie-coordinate inclusion preserves the complete fibre
norm, including the zero-dimensional case. -/
theorem norm_cmp99SUNLieCoordComplexificationLM
    {Nc : ℕ} (v : SUNLieCoord Nc) :
    ‖cmp99SUNLieCoordComplexificationLM Nc v‖ = ‖v‖ := by
  simp only [PiLp.norm_eq_of_L2,
    cmp99SUNLieCoordComplexificationLM_apply, Complex.norm_real]

/-- The same norm identity for any finite real Euclidean coordinate set;
this is only a fibre norm, never a change of the outer field norm. -/
theorem norm_finitePiLpComplexOfReal_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : FinitePiLpField ι (EuclideanSpace ℝ κ)) (i : ι) :
    ‖finitePiLpComplexOfReal x i‖ = ‖x i‖ := by
  simp only [PiLp.norm_eq_of_L2,
    finitePiLpComplexOfReal_apply, Complex.norm_real]

/-- Canonical complexification on the ordinary outer function space
agrees with the real operator after explicit coordinate transport. -/
theorem finitePiLpCanonicalComplexificationOuterCLM_ofReal
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
theorem norm_finitePiLpCanonicalComplexificationOuterCLM_ofReal_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ))
    (x : FinitePiLpField ι (EuclideanSpace ℝ κ)) (i : ι) :
    ‖finitePiLpCanonicalComplexificationOuterCLM T
        (finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal x)) i‖ =
      ‖T x i‖ := by
  rw [finitePiLpCanonicalComplexificationOuterCLM_ofReal]
  exact norm_finitePiLpComplexOfReal_apply (T x) i


end
end YangMills.RG
