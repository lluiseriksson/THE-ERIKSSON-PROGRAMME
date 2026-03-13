import Lake
open Lake DSL

package «YangMills» where
  name := "YangMills"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «YangMills» where
  roots := #[`YangMills]

-- Modules (in dependency order):
-- YangMills.Foundations.BalabanAxioms
-- YangMills.Foundations.ScaleCancellation
-- YangMills.LSI.LSI_Chain
-- YangMills.LSI.InterfaceLemmas
-- YangMills.RG.RG_Chain
-- YangMills.SpectralGap.SpectralGap
-- YangMills.ClayTheorem
