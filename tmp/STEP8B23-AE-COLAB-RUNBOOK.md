# Step 8b.23 Units A--E Colab runbook

Status: **PRE-VALIDATION**.  This is a diagnostic fresh-clone gate, not a
compiler seal and not authority to remove any PRE-VALIDATION mark.

## Immutable inputs

- Mathematical source checkpoint:
  `9429a8746a222af999d87fbfc51757d6c68a49a2`.
- Scope: 36 mathematical Git blobs, two Mathlib-only measure reproducers,
  18 ordered focal/audit bricks, and 124 independently declared axiom
  headers.  Unit F is absent.
- Runner checkpoint:
  `f00deb0c4b79749a32d25bbfb5dd7711c0ed0e38`.
- Runner Git-blob SHA-256:
  `EC3717108AEAF960216E6A16EC0D6ADAFAD5EF4B97F6BEE8DA653336F6B24C59`.
- Launcher notebook SHA-256:
  `656208736C562EE08B58356BC92D2B5C5C220608FF60997FAB9131205A1805AF`.
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

V8 verified the first three focal/audit pairs; in particular the source
Fourier normalization passed after 1227.573 seconds and its four-readout
audit passed.  The fourth focal then stopped after 145.075 seconds at the
literal normalization between the fourth power of the real Haar coefficient
and the complex coefficient `(2*pi)^(-4)`.  V9 exposes that coefficient
identity separately, rewrites the real scalar action by
`Complex.real_smul`, and runs the exact equality first as a Mathlib-only
reproducer.  No public statement, measure, physical constant or hypothesis
changes.  The retained V8 evidence/archive SHA-256 values are respectively
`C62222745BCBA7B20DCF81C5F34A3772B0A742BC6C888430452A2839B49B72AC`
and
`0D8B6F8E6405B14EBAEA3E471021E9931DF3053ED05AC27D33E9477913C4A516`.

V9 verified its isolated coefficient equality in 3.725 seconds and again
verified the first three focal/audit pairs; the Fourier focal took 1114.034
seconds.  The fourth focal then stopped after 118.573 seconds.  Elaborating
the complete module exposed the exact remaining proof-shape obligations:
normalizing the scaled interval endpoint, pinning the quotient map's source
measure, spelling the extended nonnegative-real scalar type unambiguously,
pinning the nonnegativity used by the product-measure rewrite, and rewriting
the coefficient in the syntactic form actually left by the module.  V10
changes only those measured proof terms and adds a Mathlib-only reproducer
that exercises the complete measure transport before the long focal queue.
No public statement, measure, physical constant or hypothesis changes.  The
retained V9 evidence/archive SHA-256 values are respectively
`91C5AFC9A03EF4322E4743B730E489C9FC17051702FF4EDBED2A81742FF34DF6`
and
`F642B21FD83BACEB474713FF05885B4AD6ABAA1904D6123870FABC10F722FF71`.

V10 stopped before Lean at the overlay text guard: the newly added full
reproducer opened a `noncomputable section` without its final `end`.  V11
adds only that delimiter.  The corrected reproducer passes the same local
overlay text and import-prefix guards before publication.  The retained V10
evidence/archive SHA-256 values are respectively
`F5BE79241A1F24FC1A375038E8EE6D6113A5E8B1580BF4B57DCE793DF7430390`
and
`E6BA94CB7FBFE24E9546A2F92DEE441406E0DB96B4552C3212EAE004DCA22952`.

V11 reached the full Mathlib-only reproducer and stopped there after 4.723
seconds.  It measured four API-level mismatches: negation invariance was not
materialized for Haar volume, the composed affine map retained the reversed
inverse product, sigma-finiteness is provided for `NNReal` rather than an
arbitrary `ENNReal` scalar, and the final real coefficient was inferred in a
complex target.  V12 makes exactly those choices explicit and changes no
public statement, measure, physical constant or hypothesis.  The retained
V11 evidence/archive SHA-256 values are respectively
`AB9E53A1EF9092F013D5F0F8C64E7BA69797D4CEE158A90B5201BBB1C510D3E5`
and
`FE7B2FD0E62FE219746DD736F6E60D66F88FFC339AA28681D992D6C2D938FEE3`.

## Execution contract

1. Use Colab Pro+ CPU/high-RAM, never GPU and never Windows Lean/Lake.
2. Open the one-cell launcher at its raw Git checkpoint.  Reject runner hash
   drift before executing downloaded code.
3. The runner clones the exact source checkpoint without credentials, checks
   all 36 mathematical source blobs plus the two reproducers, toolchain and
   Mathlib pins, and refuses drift.
4. Execute both measure reproducers, then the 18 focal/audit pairs in the
   frozen dependency order, and stop on the first nonzero child exit.
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
