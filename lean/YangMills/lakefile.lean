import Lake
open Lake DSL

package «YangMills» where
  name := "YangMills"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «YangMills» where
  roots := #[`YangMills]
