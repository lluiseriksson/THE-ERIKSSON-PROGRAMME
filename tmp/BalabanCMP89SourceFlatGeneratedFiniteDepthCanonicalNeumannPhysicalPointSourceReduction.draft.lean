import YangMills.RG.FinitePiLpPointSourceRightInverse
import YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalInverseProducer

/-!
SCRATCH ONLY: not imported, not compiler-verified, and not evidence.

Source-specific point-source reduction of the exact physical right-inverse
gate.  This is an equivalence, not a replacement assumption.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {M N Nc : ℕ}
variable [NeZero M] [NeZero N] [NeZero Nc]

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
