# Step 8b.23 Units A--E Colab runbook

Status: **PRE-VALIDATION**.  This is a diagnostic fresh-clone gate, not a
compiler seal and not authority to remove any PRE-VALIDATION mark.

## Immutable inputs

- Mathematical source checkpoint:
  `5317e1b051c503217cc1044abae0d323a89cd36b`.
- Scope: 36 Git blobs, 18 ordered focal/audit bricks, 124 independently
  declared axiom headers.  Unit F is absent.
- Runner checkpoint:
  `5f9dad379d0e91b6b96f2184d65a32f9ab8a0c4d`.
- Runner Git-blob SHA-256:
  `101EA30F28A7CEE3F7040C101B1FA0D1DEBCFA88B3A148F19FF0432E25C0A3F6`.
- Launcher notebook SHA-256:
  `550A685D1BF116C7F569E5CA0C4E4763D20F2635B295183C99F95A2A8EAA5255`.
- Exact Lean toolchain: `leanprover/lean4:v4.29.0-rc6`.
- Exact Mathlib commit: `07642720480157414db592fa85b626dafb71355b`.

The source checkpoint descends from the output of the fail-closed A--E
promotion writer at promoted-content manifest
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

V6 verified the first two focal/audit pairs without warnings.  The third focal
then stopped after 1212.849 seconds at two proof-shape errors in
`BalabanCMP89CenteredTorusFourierPhase.lean`: line 51 applied `ring` after
`field_simp` had already closed its goal, and line 67 did not yet normalize the
finite sum into the requested scalar product.  Under the exact-first-error
rule, V7 removes only the closed-goal tactic at line 51.  It does not change a
public statement, constant, hypothesis, or the still-unreached line-67 proof.
The retained V6 evidence/archive SHA-256 values are respectively
`8A0EBFDFFEB5436E42D2A38A4410B8CD77F59B821C4189E72EC4D5BA7B27A4EE`
and
`17EB280319A77AD256301CDCD3F943E9208C297F451AE06CF1DDA43D18B26DB0`.

V7 verified the same first two pairs and then stopped after 1220.193 seconds
at the now-first error on line 66: the target retained
`Complex.I * ∑ mu, ...`, so `Finset.sum_congr` could not yet apply.  V8 uses
the isolated `Finset.mul_sum` normalization before the congruence and removes
the simultaneously measured unused `div_one` simp argument.  No theorem
statement, physical constant or hypothesis changes.  The retained V7
evidence/archive SHA-256 values are respectively
`A235A375A6BB404EB6809642ED97CF363D4158BDB85098F211AFB1A2DFDFCBDD`
and
`824ADF76C44CB17DB557DD35CACC7C82F862C9BE0650361FC7547300C2BD24DE`.

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
