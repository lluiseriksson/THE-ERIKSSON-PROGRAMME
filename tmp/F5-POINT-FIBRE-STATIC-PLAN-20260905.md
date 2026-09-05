# F5 point/fibre prefix — static plan, not compiler evidence

## Current physical composition gate — 2026-09-05

F5 generic prefix is already cold sealed (ledger1118). Four physical
real-slice draft results passed at59f9f522 (ledger1119); three owner-map
draft results passed as a HOT prefix at6f20ead4 (ledger1120). Neither draft
group has a promoted production seal. Point-probe repair91cc4dd5 is in
flight; do not add dependent Lean modules to its immutable queue.

The source-signature review fixes a finite next composition, conditional
on acceptance of that point-probe gate, not a new analytic assumption:

1. For the literal real ambient Green G, source s, target t and whole real
   Lie vector v, rewrite the physical complex input using
   cmp99PhysicalStep7b_complexSingle_eq_pointSource_draft. Rewrite its
   output norm using norm_cmp99SourceFlowPhysicalStep7bGreen_ofReal_apply_draft.
   Apply the SEALED norm_cmp99SourceFlowFullPointSourceGreen_fibre_le_owner
   at the exact transported source/target, and use the SEALED
   norm_cmp99SUNLieCoordComplexificationLM on v. No outer norm transport,
   dimension factor, free Green or equality hypothesis is admissible.
2. Rewrite both block owners with
   cmp99PhysicalStep7b_blockSite_eq_sourceLocalizationOwner_draft.
   The sealed bound has distance(sourceOwner,targetOwner); the real typed
   kernel consumer has distance(targetOwner,sourceOwner). Use the named
   finBoxDist_comm (PhysicalBondDistance.lean), not an adjoint/row argument.
   The endpoint is literally ||G(singleFinitePiLp s v) t|| <=
   (ownerAmplitude R a_j rho * exp(-(rho*dist(owner t,owner s))))*||v||.
3. Instantiate finitePiLpTypedBlockLocalizedSupBound_of_kernel_fibre_card
   with that literal G and N=R^4, using
   card_cmp99SourceLocalizationOwner_fibre_draft, then consume
   exists_cmp85SourceFullGreen_uniformOwnerAmplitude. Choose rho,C once
   before depth, K,Q,Nc; retain the output amplitude C*R^2 exactly,
   because R^4*(C*(R^2)^-1)=C*R^2 for positive R=L^(depth+1).
   cmp99SourceFlowFlatFullComplexA and cmp99SourceMassParameter must be
   related by their actual definition (SourceFlowFlatPrecisionScalarDictionary),
   not by a new freely supplied coefficient equality.

This closes only the full ambient value action, not a proper regional
inverse or derivatives. The R^2 is the value-action scale, not uniform B0.
No all-owner count (2*K*Q)^4 enters. Required evidence: the two point-probe
declarations first; then the exact finite promotion/assembly with separate
audits and preserved source hashes. Counters remain20/41,TermSource0.

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

## Point-probe transport acceptance gate (static review, 2026-09-05)

The next point-probe lemma must identify the entire transported input,
not merely its norm: the physical carrier map applied to the outer
complexification of `singleFinitePiLp source v` equals
`cmp99FlatComplexFibrePointSource (siteEquiv source)
  (cmp99SUNLieCoordComplexificationLM Nc v)`.
The point-source definition is in
`BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction.lean`;
it is exactly `fun x => if x = source then v else 0`.

Proof route: evaluate at an arbitrary transported site, use the named
carrier evaluation theorem, then split equality with the source and use
coordinate extensionality inside the Lie fibre. Pin carrier and fibre
types explicitly. Do not assume this equality from the existing Green
intertwining theorem. The already cold-sealed
`norm_cmp99SUNLieCoordComplexificationLM` then preserves the same whole
Lie-vector norm without a dimension factor. No outer norm equivalence
is needed or asserted.

This is a static acceptance plan only, not a new compiled declaration.
The active retry-v2 queue is unchanged. At the read-only probe around
13:29 UTC, launcher PID615 remained active and prerequisites had reached
8521/8674; the carrier repro had exit0. The physical four-theorem draft
had not yet produced a verdict. Counters remain20/41 and TermSource0.

The exact input transport is now written separately in
`tmp/SourceFlowPhysicalPointProbeDraft.lean`: canonical complexification of
a real single-site probe, then transport by the physical Step-7b site map.
Only sealed dependencies are imported; the pending physical Green draft
is not imported. Both declarations remain PRE-VALIDATION and uncompiled.
The exact one-file manifest is `tmp/f5_point_probe_paths.txt`. Text guard
passed in0.03108s/20,639,744 peak bytes, import-prefix guard in0.01284s/
20,017,152 peak bytes, each one local process and no Lean. These are only
textual checks, not evidence of elaboration or mathematical correctness.
No active runner, source pin or queue changed. Before a remote diagnostic,
the new reindexing/conditional proof must have its Mathlib-only repro
prepared and run first; do not pay a new project bootstrap to test it.

That repro is now prepared in `tmp/SourceFlowPointProbeRepro.lean` with
only `Mathlib.Analysis.InnerProductSpace.PiL2`: conditional point-source
transport under piCongrLeft and coordinatewise real-to-complex conditional
transport. It remains uncompiled. The manifest now covers BOTH files;
rerun text guard PASS0.02255s/20,647,936 peak bytes and import-prefix
guard PASS0.01435s/19,693,568 peak bytes. Neither was added to retry-v2.
