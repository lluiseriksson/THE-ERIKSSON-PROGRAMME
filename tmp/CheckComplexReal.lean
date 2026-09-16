import Mathlib.Analysis.Complex.RealDeriv
import YangMills.RG.BalabanCMP116FTCInterpolation

#synth NormedSpace ℝ ℂ
#check HasDerivAt.comp_ofReal
#check @HasDerivAt.comp_ofReal
#check Complex.continuous_ofReal
#check YangMills.RG.cmp116FTC_oneStep
#synth SMul ℝ ℂ
#check Complex.instRCLike.toSMul
example (f : ℝ → ℂ) (f' : ℂ) (x : ℝ) : Prop := HasDerivAt f f' x
example : ContinuousSMul ℝ ℂ := by
  constructor
  simpa [Complex.real_smul] using
    (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
#synth IsBoundedSMul ℝ ℂ
