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

-- Mathlib is pinned to an exact commit for reproducibility.  This SHA is the
-- one already resolved in `lake-manifest.json`; pinning it here (rather than
-- `@ "master"`) means even `lake update` reproduces the exact verified state.
-- To rebuild the verified core: `lake build YangMillsCore` (see REPRODUCIBILITY.md).
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "07642720480157414db592fa85b626dafb71355b"

lean_lib «MarkedRootedClosure» where
  -- C1 paper endpoints (lean-rooted-tree-polymer-expansion, integrated
  -- 2026-07-11; exact applications of pinned core theorems)
