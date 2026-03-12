import Lake
open Lake DSL

package «YangMills» where
  -- add package configuration options here

lean_lib «YangMills» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"
