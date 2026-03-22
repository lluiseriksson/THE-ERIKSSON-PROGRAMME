import YangMills.ClayCore.BalabanRG.P91CorrectedWindowPublicShim
import YangMills.ClayCore.BalabanRG.P91UniformDriftWindowDirect

namespace YangMills.ClayCore

/-
v0.9.31

This file is intentionally small: it does not create a new analytic hub.
It provides a stable theorem-side consumer packet for the corrected P91 lane,
so downstream files can migrate away from deprecated legacy imports one by one.
-/

namespace P91CorrectedWindowConsumerPacket

/-- Stable theorem-side alias to the corrected-window β-growth / AF result. -/
abbrev betaGrowth := asymptotic_freedom_implies_beta_growth_corrected_in_window_mul
/-- Stable theorem-side alias to the corrected-window denominator control. -/
abbrev denominatorControl := denominator_in_unit_interval_corrected_in_window_mul
/-- Stable theorem-side alias to the direct multiplicative-window drift theorem. -/
abbrev linearDrift := beta_linear_drift_P91_corrected_in_window_mul
/-- Stable theorem-side alias to the corrected-window β ≥ 1 inductive invariant. -/
abbrev betaGeOneAll := beta_ge_one_all_in_window_mul_direct
/-- Stable theorem-side alias to the corrected multiplicative-window surface. -/
abbrev windowSurface := asymptotic_freedom_implies_beta_growth_corrected_in_window_mul

/-- The consumer packet exists and is intended as the stable theorem-side entrypoint
for the corrected multiplicative-window P91 lane. -/
theorem packet_sanity : True := by
  trivial

end P91CorrectedWindowConsumerPacket

end YangMills.ClayCore
