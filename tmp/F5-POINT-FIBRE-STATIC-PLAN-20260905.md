# F5 point/fibre prefix — static plan, not compiler evidence

F4 cold source remains `5138e9bd4bc88797c91c21df5bb5c630c71600ca`.
Nothing in this plan changes the graph being compiled or its acceptance gate.

## Finite prefix

1. Mathlib-only `FullGreenFibreNormRepro.lean`: exact common-scalar norm
   and isometric real-coordinate inclusion. Run before project elaboration.
2. `SourceFlowFullPointSourceFibreBoundDraft.lean`: two declarations;
   use the sealed F3 *equality* with a common scalar for every Lie coordinate.
   The fibre norm costs no `Nc^2-1` factor, even for an empty coordinate type.
3. `FinitePiLpRealSliceFibreTransportDraft.lean`: four declarations;
   real inclusion preserves a fibre norm, and canonical complexification
   intertwines the real operator. Outer `PiLp`/function equivalence only
   transports coordinates, never an asserted isometry of outer norms.
4. Existing `FullGreenOwnerFibreActionDraft.lean`: one declaration;
   supported-source sum pays the cardinality of exactly one owner fibre.
   Physical implementation uses `blockOf_card` in `BlockLattice.lean`,
   not a fresh proof of the block-offset equivalence. The active-region
   inequality already exists as
   `card_cmp99Eq342SourceLocalizedActiveOwner_fiber_le`.

All draft declarations remain PRE-VALIDATION pending promoted cold validation.
The seven declarations passed HOT diagnostics v2/v3 on 2026-09-05 (ledger1117):
six in the real-slice/point-fibre files, one in the corrected owner action.
Both repro errors and their raw evidence remain archived. The first three
files depend only on already sealed F3 or generic imports, not on an
unverified F4 result. F4 itself is now separately cold sealed (ledger1116).

## Physical composition still required

The source-flow physical Green is an operator on an ordinary outer function
space. `FinitePiLpTypedBlockLocalizedSupBound` uses outer counting `PiLp`.
Use the explicit outer equivalence together with coordinate evaluation;
do not identify these normed-space structures by definition.

The existing `cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv` is a
site permutation `U`. Its norm is not needed: the real-slice dictionary
should expose `(U G_complex U.symm)(U (ofReal f))` at `U.site x`, reducing
to `ofReal (G_real f x)` by the named canonical complexification theorem.
The actual source-flow Green, not a separately supplied operator, must be
the one appearing in this endpoint.

The F3 owner distance is written source/target. For the output-fixed
consumer use symmetry of `finBoxDist`, not a generic adjoint/row argument.
The owner fibre count is `R^4`; F4 retains `R^-2`, so the value action pays
exactly `R^2`. No total-owner count `(2*Kloc*Q)^4` belongs in the constant.

This point/fibre prefix is not the regional inverse dictionary. Restricting
the ambient inverse is not identified with the inverse of a compression.
It does not prove the three derivative actions or attain window 15.
The existing derivative adapter uses spacing `R*eta`; actual fine spacing
`R^-1` requires `eta=R^-2`, whose costs must not be suppressed.

Counters: 20/41, TermSource=0. No PRE retirement, root claim, regional B0,
uniform derivative estimate, or contraction follows from this hot prefix.

## Next finite checkpoint

Promote the real-slice, point-fibre and owner-action drafts with seven public
axiom declarations in separate audits. Compare mathematical text under an
explicit finite renaming table; no constants, hypotheses or scope changes.
Then prepare a fresh immutable-source cold graph, not a retained-runtime
retry. The 2026-09-05 runtime was deleted after archive verification.

## Physical real-slice draft prepared during the promoted cold gate

The promoted source is now `6c49a8daeb6d6c6f60ac4a2cd2bafda67a495ff4`;
its fresh cold gate started 2026-09-05 11:46:36 UTC. No result is inferred
from that start. The new source below is NOT part of that cold checkpoint.

`tmp/SourceFlowPhysicalGreenRealSliceDraft.lean` contains four proposed
theorems: literal ambient real-slice identity, evaluation of the existing
carrier permutation, literal Step-7b real-slice identity, and exact output
fibre norm. Every operator is the existing source-flow Green; no arbitrary
Green or assumed intertwining identity occurs in their hypotheses.

`tmp/SourceFlowPhysicalCarrierRepro.lean` isolates the two Mathlib-only
steps (piCongrLeft evaluation and cancellation under conjugation). It must
run first, then the physical draft, and only after the F5 cold gate passes.
Both files remain PRE-VALIDATION, with no compiled claim or root import.
Overlay textual and import-prefix checks passed the exact two-file list;
the import check used 0.038 seconds and 17,563,648 bytes peak RSS locally.
No Windows Lean/Lake was used.

This does not discharge the owner-cardinality action, proper regional
inverse, derivative actions, regional B0 or window15. Counters unchanged.

The physical hot runner is published at
`5e65c2d0e79e26a1e8e070f9dfc8f08351e16aa7` (source draft `e833ec7e7`).
Its subsequent synthetic control-flow test passed eight cases: success,
cold FAIL, incorrect cold hash, verifier exit9, repro exit7, forbidden
axiom, absent compiled output and duplicate start. All subprocess/HTTPS
calls were mocked. 0.7234 seconds, 32,608,256 bytes peak RSS; Lean evidence0.

Before the later owner-action endpoint, expose these exact remaining maps:

1. Transport a real `singleFinitePiLp` by the physical carrier equivalence
   to `cmp99FlatComplexFibrePointSource` at the mapped source, with the
   same complexified Lie vector. A field identity alone is not this lemma.
2. Identify `cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv` with
   `cmp99Eq389SourceLocalizationSiteEquiv` (or prove their block owners
   agree). The first composes the generated full/Step7b maps; the second
   is an explicit cast. Their common domain/codomain is not a proof.
3. Use `blockOf_card` for exactly one owner fibre and transport that count
   through the proven map. Retain `R^4 * (C * R^-2) = C * R^2`.

These are parts of the already named physical coordinate/owner dictionary,
not claims that the pending four-theorem hot draft proves them.

The source read resolves the design question in item2 favorably:
`cmp99GeneratedFineBoxOneBlockEquiv` in
`BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse.lean` is itself
`Equiv.cast`, with a named `..._apply_val` theorem preserving every fine
coordinate. The full-site equivalence in
`BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary.lean`
is also a size cast, after forgetting the full-region membership proof.
Thus the route is coordinate-value extensionality of those casts, not a
new geometric relabeling. Still write the exact equality as a theorem
before transporting source-localization owners; this static reading is not
compiler evidence for that equality.

## Prepared owner dictionary, not added to the active queues

`tmp/SourceFlowPhysicalOwnerDictionaryDraft.lean` now proposes the exact
site-equivalence equality, its block-owner corollary and the full ambient
owner-fibre cardinality `(L^(depth+1))^4` by `blockOf_card` and a bijection.
`tmp/SourceFlowOwnerCastRepro.lean` isolates the size-cast coordinate lemmas
with Mathlib only. Both depend on sealed carrier definitions, not on the
pending F5 promoted/hot lemmas. Both remain PRE-VALIDATION, uncompiled.

The exact two-file textual/import guards passed, respectively0.0673s/
18,407,424 bytes and0.0513s/17,563,648 bytes peak RSS. No Lean was invoked.
Do not silently append these files to the running cold gate or the already
published four-theorem physical hot runner. They form the next separately
prepared unit after the current evidence is preserved.
