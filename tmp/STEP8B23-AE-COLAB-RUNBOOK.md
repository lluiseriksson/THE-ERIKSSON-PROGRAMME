# Step 8b.23 Units A--E Colab runbook

Status: **PRE-VALIDATION**.  This is a diagnostic fresh-clone gate, not a
compiler seal and not authority to remove any PRE-VALIDATION mark.

## Immutable inputs

- Mathematical source checkpoint:
  `393be82998cd34c455c886827e21ac2c9f7229e9`.
- Scope: 36 Git blobs, 18 ordered focal/audit bricks, 124 independently
  declared axiom headers.  Unit F is absent.
- Runner checkpoint:
  `735dab7248cb2cc5aebe79033b560be6a4aa33a7`.
- Runner Git-blob SHA-256:
  `A80C93C96285BDA9767D954E74E244ACACE7025EC891756725B357165E42A994`.
- Launcher notebook SHA-256:
  `4A950126D4A9981AA5F15FD5956CEC16A84D83993DBD53E7630180F8583043A4`.
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
