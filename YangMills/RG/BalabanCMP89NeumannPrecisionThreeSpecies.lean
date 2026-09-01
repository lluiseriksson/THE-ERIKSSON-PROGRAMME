import YangMills.RG.BalabanCMP89SourceNeumannRegionalGaugePrecision

/-!
# PRE-VALIDATION: literal three-species split of the CMP89 Neumann precision

The source is present, but its `.olean` has not yet been materialized and the
result has not yet been verified by the compiler.

This module exposes, as an operator equality, the three separately budgeted
parts of the precision printed in CMP89 (2.44): the internal-bond Neumann
Laplacian, the bare scalar mass squared, and the generated adjoint-average
term.  Composition with an arbitrary candidate Green distributes over those
same three terms literally.

No reflection identity or estimate is proved here.  In particular, this
split cannot manufacture the full right-inverse equation from three unrelated
bounds.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Literal operator decomposition with the three source species visible. -/
theorem cmp89SourceNeumannRegionalGaugePrecision_eq_threeSpecies
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass a : ℝ) :
    cmp89SourceNeumannRegionalGaugePrecision
        Omega rho U Qprime spacing mass a =
      (cmp89SourceNeumannRegionalLaplacian Omega rho U spacing +
        mass ^ 2 • ContinuousLinearMap.id ℝ
          (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))) +
        a • (Qprime.adjoint.comp Qprime) := by
  rfl

/-- Composing with one candidate Green preserves the literal three-species
split.  This is the exact assembly interface for the separate Laplacian,
mass and `Q′*Q′` reflection proofs. -/
theorem cmp89SourceNeumannRegionalGaugePrecision_comp_eq_threeSpecies
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass a : ℝ)
    (G : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    (cmp89SourceNeumannRegionalGaugePrecision
        Omega rho U Qprime spacing mass a).comp G =
      (cmp89SourceNeumannRegionalLaplacian
          Omega rho U spacing).comp G +
        ((mass ^ 2 • ContinuousLinearMap.id ℝ
          (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))).comp G) +
        ((a • (Qprime.adjoint.comp Qprime)).comp G) := by
  apply ContinuousLinearMap.ext
  intro phi
  simp only [cmp89SourceNeumannRegionalGaugePrecision,
    cmp99SourceGaugePrecision, cmp85BareMassPrecision,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  rfl

end

end YangMills.RG
