# C6d Eq. (3.36) physical-adjoint hot diagnostic

- Verdict: `PASS` (diagnostic hot-cache gate; not a cold promotion seal).
- Source checkpoint: `010502d5f48f542856b9c567e97bdc274e65f276`.
- Runner revision: `c6d-eq336-adjoint-hot-debug-v15`.
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`.
- Lean toolchain asset SHA-256: `bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e`.
- Canonical evidence payload SHA-256: `bdfaf427d2a40423837e91f0a51e84f44ade194e71133c5f2f2ff33da5600dcd`.
- Stored `evidence.json` SHA-256 (payload plus terminal newline): `afb4d83313066a4094a691c0f2d46c4f1774759add85b6dd1c10396066d916db`.
- Downloaded archive SHA-256: `7443d6ab74e00d5fda1ef920bf96d052aa93ca708eee5a83986095f236113b81`.

The complete queue passed with real child exit codes: regular-cube source/audit,
the Eq. (3.35) forward/witness/class chain, the finite summation-by-parts
reproduction, and the Eq. (3.36) physical source/audit.  The Eq. (3.36) audit
printed 17 allowed axiom blocks (`propext`, `Classical.choice`, `Quot.sound`)
and one declaration that depends on no axioms.

This evidence verifies the scratch implementation in a retained Colab build
graph.  It does not remove `PRE-VALIDATION`, promote the modules, move the
`20/41` terminal counter, or show that window 15 is attained.  Those actions
require the separate cold-checkout seal.
