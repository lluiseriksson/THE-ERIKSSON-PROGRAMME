# Step 8b.23 Units A--E Colab runbook

Status: **PRE-VALIDATION**.  This is a diagnostic fresh-clone gate, not a
compiler seal and not authority to remove any PRE-VALIDATION mark.

## Immutable inputs

- Mathematical source checkpoint:
  `339afb22dd296977a2ee43623ae7e89e77f538ce`.
- Scope: 36 Git blobs, 18 ordered focal/audit bricks, 124 independently
  declared axiom headers.  Unit F is absent.
- Runner checkpoint:
  `4a196e56d6565daac4314bdbd2ec37c6116db297`.
- Runner Git-blob SHA-256:
  `7101C7F9CF7D924D31B00A137821C6B4F8B7C53EB16948169520580DFBEDAA3C`.
- Launcher notebook SHA-256:
  `A435C6799F5ED62E7944D0AA6D0B30E921D658B780FBE028C46334BE13A04459`.
- Exact Lean toolchain: `leanprover/lean4:v4.29.0-rc6`.
- Exact Mathlib commit: `07642720480157414db592fa85b626dafb71355b`.

The source checkpoint is the output of the fail-closed A--E promotion writer
at promoted-content manifest
`C1057D840543EB2EF8024B8F90B7D9B785DF7C40D5C15582E3F4E83022F41AD0`.
Every source/audit file retains its visible PRE-VALIDATION header.

The v1 diagnostic is retained as a measured failure at
`BalabanCMP89CenteredBrillouinAffineSlice.lean:52`: its generic real scalar
action did not definitionally match complex multiplication.  V2 changes only
that spelling and the diagnostic transport; no theorem statement, constant or
hypothesis changed.

V2 measured that merely changing the displayed target to a real scalar action
still let simplification normalize the two scalar structures differently.  V3
rewrites explicitly with `Complex.real_smul` before applying the generic affine
slice theorem.  Again, the public statement and all physical data are unchanged.

V3 measured that rewriting the generic theorem directly still failed to
specialize across the scalar-action boundary.  V4 replaces that rewrite by an
explicit `calc` step and proves only the final affine argument identity under
the integral.  The public statement remains unchanged.

V4 verified the first focal and its two-readout audit.  The queue then stopped
at `BalabanCMP89CenteredUnitCubeTorusQuotient`: one missing measure-theory
import exposed the remaining mechanical API/proof-shape incompatibilities in
that module.  V5 adds that exact import, makes the quotient-map namespace and
coordinatewise continuity explicit, replaces obsolete update rewrites by
their definitions, and proves the endpoint/final-replacement orientations
directly.  It also replaces the first brick's two linter-producing tactics by
the equivalent `ring_nf`.  No public statement, physical constant or
hypothesis changes.

V5 verified the first focal/audit pair without warnings and reduced the second
brick to one literal endpoint normalization in the one-coordinate
measure-preserving theorem.  V6 supplies that equality while pinning the
coordinate map's type; no public statement or measure is changed.

## Execution contract

1. Use Colab Pro+ CPU/high-RAM, never GPU and never Windows Lean/Lake.
2. Open the one-cell launcher at its raw Git checkpoint.  Reject runner hash
   drift before executing downloaded code.
3. The runner clones the exact source checkpoint without credentials, checks
   all 36 source blobs, toolchain and Mathlib pins, and refuses drift.
4. Execute the 18 focal/audit pairs in the frozen dependency order and stop on
   the first nonzero child exit.
5. Require exactly 124 axiom headers and reject `sorryAx`, `ofReduceBool` or
   any axiom outside `{propext, Classical.choice, Quot.sound}`.
6. Preserve every child's complete combined output as a hash-checked stage
   log inside the evidence archive.  Request archive download before runtime
   release and retain the executed notebook separately.
7. A diagnostic PASS prepares a later cold terminal checkpoint.  It does not
   itself remove PRE-VALIDATION, import the modules into `YangMillsCore`, or
   authorize Unit F.

## Honest scope

This queue proves only elaboration and axiom cleanliness of source-specific
Units A--E.  It does not construct regional `B0`, attain physical window 15,
install a new `PreEq136` producer, prove CMP116 (1.36), or inhabit
`TermSource`.  The hard counters remain `20/41` and `TermSource = 0`.
