import Lake
open Lake DSL

package «YangMills» where
  -- add package configuration options here

lean_lib «YangMills» where
  -- add library configuration options here

/-- The sound, self-contained core (no sorry, no project axioms, no LSI sprawl).
    Build with `lake build YangMillsCore`.  See `YangMillsCore.lean`. -/
lean_lib «YangMillsCore» where
  -- only the salvaged core modules are reachable from the `YangMillsCore` root

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"
