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

All draft declarations remain PRE-VALIDATION. No new mathematical theorem
has yet passed Lean. The first three files depend only on already sealed
F3 or generic imports, not on an unverified F4 result.

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
uniform derivative estimate, or contraction follows from textual guards.
