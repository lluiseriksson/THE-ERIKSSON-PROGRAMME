import YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ} [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

example (hd : 2 ≤ d) (hM : 2 ≤ M)
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d (M * N))
    (hSmall : OmegaSmall.BlockSaturated)
    (hLarge : OmegaLarge.BlockSaturated)
    (background : GaugeConfig d (M * N) (SUN Nc))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hno : cmp99SourceUbarFineDeviationRadius d M epsilon <
      cmp99UbarNoWindingThreshold Nc)
    (hfine : ∀ e : ConcreteEdge d (M * N),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    (CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM OmegaSmall
      background hSmall epsilon hepsilon hno hfine).toSourceScale.data.nextBackground =
    (CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM OmegaLarge
      background hLarge epsilon hepsilon hno hfine).toSourceScale.data.nextBackground := by
  rfl

end

end YangMills.RG
