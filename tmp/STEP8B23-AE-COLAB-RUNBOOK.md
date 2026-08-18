# Step 8b.23 Units A--E Colab runbook

Status: **PRE-VALIDATION**.  This is a diagnostic fresh-clone gate, not a
compiler seal and not authority to remove any PRE-VALIDATION mark.

## Immutable inputs

- Mathematical source checkpoint:
  `b7f46dd81b4c0fde311f80c148e130aec943d19d`.
- Scope: 36 Git blobs, 18 ordered focal/audit bricks, 124 independently
  declared axiom headers.  Unit F is absent.
- Runner checkpoint:
  `5942ee522a92f5945bb5d7e22c6fa237edfbdd7a`.
- Runner Git-blob SHA-256:
  `0DCB106CF6116953F07F26BFC078DD608BDC27AE8EA70213C294C40B8B123283`.
- Launcher notebook SHA-256:
  `93B97E43F02DDFD2DF0FB38ADCE9C8A81AC51B748F439913AEE62763000B3C59`.
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
