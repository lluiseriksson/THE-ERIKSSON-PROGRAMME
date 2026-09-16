import YangMills.RG.BalabanCMP98GAdInverse

open Matrix
open scoped Matrix.Norms.L2Operator

#check @YangMills.RG.cmp98GAd
#check @YangMills.RG.norm_cmp98GAd_sub_id_le_exp_sub_one
#check @ContinuousLinearMap.le_opNorm
#synth NormedRing (Matrix (Fin 2) (Fin 2) ℂ)
#synth NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ)
