import YangMills.RG.FinitePiLpPointSourceRightInverse
import YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalInverseProducer

/-!
# PRE-VALIDATION: point-source reduction of the physical CMP89 right inverse

The source is present, but its `.olean` has not yet been materialized and the
result has not yet been verified by the compiler.

This module specializes the finite point-source criterion to the exact
source-faithful physical CMP89 right-inverse gate.  The result is an
equivalence: the family of point-source equations neither weakens nor
strengthens the operator identity, and all geometry and scalar conventions
remain fixed internally by the physical producer.

No point-source equation is proved here.  In particular, this reduction does
not supply the Laplacian or `Q′*Q′` reflection identities required by CMP89
(2.42).
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {M N Nc : ℕ}
variable [NeZero M] [NeZero N] [NeZero Nc]

/-- The exact physical right-inverse equation holds if and only if it holds
on every literal coordinate point source of the terminal regional field. -/
theorem
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalRightInverse_iff_pointSources
    {m : Fin 4 → ℤ}
    (hM : 2 ≤ M) (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (steps : ℕ) (mass aSource : ℝ) :
    CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalRightInverse
        (Nc := Nc) hM hm hfit steps mass aSource ↔
      let Omega := cmp89SourceNeumannRectangleActiveRegion (N := N) m
      let spacing :=
        cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing
          M steps
      let precision :=
        cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
          (Nc := Nc) (by norm_num) hM Omega steps spacing mass aSource
      let siteEquiv := cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv
        (M := M) (N := N) hm hfit (steps + 1)
      let fullGreen :=
        cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalFullGreen
          (Nc := Nc) hM Omega steps mass aSource
      ∀ source v,
        precision
            (cmp89NeumannScalarReflectionOperator
              (g := SUNLieCoord Nc) siteEquiv fullGreen
              (singleFinitePiLp source v)) =
          singleFinitePiLp source v := by
  unfold CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalRightInverse
  exact finitePiLp_comp_eq_id_iff_pointSources _ _

end

end YangMills.RG
