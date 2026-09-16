# Gate 8 post-seal design scratch

This scratch file is not an evidence artifact and is not part of the source
checkpoint.

## Mass-zero complex floor

The vertical-variation theorem already assumes only
`CMP89Eq251UniformMassWindow mass`.  The obsolete `0 < mass` occurs only when
the existing complex-floor proof calls the real-slice lower bound.  A parallel
three-theorem module can reuse the proof literally and call
`cmp89Eq249CentralStabilizedLowerConstant_le_re_massUniform` instead:

1. lower-minus-variation is below the complex denominator norm;
2. the denominator is nonzero under the same scalar window;
3. the reciprocal obeys the same explicit bound.

The draft is
`tmp/BalabanCMP89Eq249CentralStabilizedComplexFloorMassUniform.draft.lean`.

Once that three-theorem core is sealed, the remaining uses of the older
positive-mass theorem are localized in six source modules:

- `BalabanCMP89Eq248FineLatticeNormalizedFourierGreen`;
- `BalabanCMP89Eq251CommonStripHolomorphy`;
- `BalabanCMP89Eq251ComplexStabilizedEndpointBound`;
- `BalabanCMP89Eq251FineLatticeStabilizedEndpointBound`;
- `BalabanCMP89Eq251StabilizedBoundarySeam`;
- `BalabanCMP89Eq251StabilizedEndpointHolomorphy`.

In each case the first static question is whether `0 < mass` is used for
anything except the old central nonvanishing/reciprocal theorem.  Do not
blanket-copy the API until that use check is complete.  The physical
mass-zero denominator nonvanishing already sealed downstream is not a
substitute for these common-strip endpoint statements.

Static use check (2026-08-15): in the base common-strip theorem and both
endpoint-bound theorems, `hmassPos` is consumed only by the old central
nonvanishing/reciprocal call.  The remaining occurrences in the normalized
Fourier Green, boundary seam and endpoint-holomorphy modules are propagated
through their corresponding composite theorem calls; no independent
positive-mass estimate appeared in the grep/use slices.  This supports
parallel mass-uniform variants after the core seal, while keeping the old API
for compatibility.  It is still not a proof of the RG mass-flow window.

Do not use `cmp99SourceMassParameter` to discharge
`CMP89Eq251UniformMassWindow mass`.  Despite its Lean name, that recurrence
is the printed averaging coefficient `a_j`: downstream denominators pass it
in their `a` slot while retaining the physical `mass` as a separate argument.
The elementary bound `0 < a_j <= a` is therefore irrelevant to the physical
mass-square window.  Identifying the two would be a type-correct but
source-false dictionary.  Preservation or specialization of the physical
mass window remains a separate named debt.

## Centered alias reflection

Do not define the reindexing by literal integer negation: the half-open
centered carrier is not closed under it at the lower endpoint.  Also do not
reuse `cmp99SourceFlatQprimeSignedCenteredAliasEquiv` as a reflection of an
existing alias representative: that equivalence maps a physical quotient
residue `q` to the centered representative of `-q`; its input is not an
already centered alias integer.

The faithful alias reflection must pass through the actual residue:

`centered representative -> ZMod M -> negation -> canonical Fin M -> centered representative`.

The existing sealed maps make the safe construction more precise.  First
build the residue-preserving equivalence from the centered subtype to
`ZMod M` as

`signedCenteredAliasEquiv.symm -> ZMod.finEquiv -> residue negation`.

Indeed, the sealed signed theorem says that the centered output represents
the *negative* of its `Fin M` input, so the final negation recovers the cast of
the original centered integer.  Conjugating residue negation by that
equivalence then gives the required permutation of the centered subtype.
This avoids the false shortcut through
`cmp99SourceFlatQprimeCenteredAliasEquiv`: that map is an order-preserving
enumeration (`lower + q`), not a residue-preserving equivalence.

Its acceptance lemma must state that the output integer cast in `ZMod M` is
the negative of the input integer cast.  The vector and depth-one alias-index
permutations should be products of this scalar permutation, and complete sums
must be reindexed with `Equiv.sum_comp`.

Static type gate: do not insert the vector reflection directly after
`cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv`: its codomain is
`CMP89Eq246AliasIndex d M 1`, only explicitly equivalent (via the sealed
depth-one bridge) to the vector carrier with `M`.  The consumer-facing route
therefore defines a named reflection on `AliasIndex ... 1` by conjugating the
vector reflection through
`cmp99SourceFlatQprimeAliasIndexOneVectorEquiv`, proves that intertwining
identity.  Treating `M ^ 1` and `M` as definitionally equal is a type-level
version of the dictionary shortcut the brick is meant to eliminate.

Do **not** conjugate this alias reflection to a permutation of one fixed
physical coarse fibre.  At fixed `ell`, negating the alias representative
changes `z(ell) + 2*pi*m` to `z(ell) - 2*pi*m`, not to the full opposite
momentum `-z(ell) - 2*pi*m`.  Unless the coarse residue is self-opposite, the
missing `-z(ell)` lives in the distinct coarse fibre
`cmp99FinBoxFourierNeg ell`.  A fixed-fibre permutation would therefore be
type-correct algebra with the wrong physical meaning.

The physical bridge must instead start by constructing an equivalence

`FixedCoarseFibre ell ≃ FixedCoarseFibre (FourierNeg ell)`

from periodic fine-momentum negation, first prove that `coarseAlias` commutes
with that negation.  Complete sums may be reindexed only through that
cross-fibre equivalence.

Concrete factorization after that carrier bridge:

`signedAliasEquiv(ell).symm -> fibreFourierNeg(ell) ->
 signedAliasEquiv(FourierNeg ell)`.

This conjugate is an exact permutation of the printed depth-one alias carrier
*parameterized by `ell`*.  It is the correct consumer-facing affine-carry
map; it is not `cmp99SourceAliasIndexOneReflection`.  Its first acceptance
theorem is the commuting square with the two signed physical-fibre
dictionaries.  Its second acceptance theorem must expose the quotient law
coordinatewise in `ZMod M`: target quotient equals `-q` when the corresponding
coarse residue is zero and `-q-1` otherwise.  Only after that explicit
zero/nonzero split may the full coarse-plus-alias momentum and complete-sum
reindexing be stated.  Defining the conjugate alone is construction, not a
proof that the carry has the advertised closed form.

The coordinate arithmetic to expose is finite and has two literal cases.
Write the fine representative as

`k = ell.val + N' * q.val`, with `0 <= ell.val < N'` and `0 <= q.val < M`.

- If `ell.val = 0`, periodic negation has quotient residue `-q` in `ZMod M`.
- If `ell.val != 0`, then
  `M*N' - k = (N' - ell.val) + N' * (M - q.val - 1)`, so the target quotient
  residue is `-q-1` in `ZMod M`.

This is the theorem the conjugate must cite.  Its proof should expose the
zero/nonzero split and the Euclidean reconstruction lemma
`cmp99SourceFlatQprimeFixedCoarseFibreEquiv_symm_apply_val`; a bare `simp`
through the conjugated equivalences is not an acceptable substitute.  Since
the signed alias dictionary represents `-q`, the resulting output alias
represents `q` in the zero branch and `q+1` in the nonzero branch.  Keep the
quotient law and the induced signed-alias law as separate named statements.

Proposed proof boundary (names provisional, statements mandatory):

1. `cmp99FinBoxFourierNeg_apply_val`: the periodic negative representative
   has value `0` at value `0`, and `N-k.val` otherwise.  Derive it from
   `cmp99FinBoxZModEquiv_fourierNeg` and `ZMod.neg_val`; do not restate
   periodic negation as data.
2. `cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv_quotient_cast`:
   after the zero/nonzero split on `ell mu`, the quotient returned by the
   target fixed-fibre equivalence is `-q` or `-q-1` in `ZMod M`.  This is the
   Euclidean carry theorem and must mention both fibres explicitly.
3. `cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv_cast`:
   transport item 2 through the two sealed signed dictionaries.  This is an
   alias statement, not the quotient theorem itself.  Coordinatewise its
   closed form is

   `cast (carry ell m) = - cast m + (if ell.val = 0 then 0 else 1)`

   in `ZMod M`: the input signed alias represents `-q`, whereas the output
   signed alias represents the negative of the carried target quotient.

Static composition check (2026-08-15): the existing signed dictionary theorem
gives `cast m = -q`, while the sealed carrier reflection gives
`cast (reflection m) = -cast m = q`.  Negating the quotient-carry identity
gives `-q' = q + c(ell)`.  Therefore the next consumer-facing theorem can be
stated directly as

`cast (signedAlias(k')) = cast (AliasIndexOneReflection (signedAlias(k))) + c(ell)`.

This factors the affine map into the already sealed residue reflection plus
one explicit coordinatewise translation.  It must remain an equality of
represented residues; literal integer equality in the half-open centered
carrier would fail at the wrap endpoint.

Exact theorem-level composition after the quotient brick is sealed:

- write `m` and `m'` for the two outputs of
  `cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv`, at `ell` and
  `cmp99FinBoxFourierNeg ell` respectively;
- expose coordinates with
  `cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv_apply`;
- rewrite both coordinate casts using
  `cmp99SourceFlatQprimeSignedCenteredAliasEquiv_cast_eq_neg`;
- rewrite `-q'` using
  `cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv_quotient_cast`;
- rewrite the reflected input cast using
  `cmp99SourceCenteredAliasVectorReflection_coordinate_cast_eq_neg`.

The remaining goal is ring arithmetic in `ZMod M`, with the carry kept as
`if (ell mu).val = 0 then 0 else 1`.  No centered-integer case split is
needed and no equality in `ℤ` should be introduced.  This also pins the
consumer import boundary: the next module imports the quotient-carry brick,
the signed momentum dictionary and centered-alias reflection; the quotient
brick itself remains independent of reflection.

The conjugated alias permutation itself should be defined, without new data,
as the composite

`signedIndexEquiv(ell).symm -> fibreFourierNeg(ell) -> signedIndexEquiv(-ell)`.

Its commuting-square theorem is therefore definitional.  In the coordinate
proof, name `k := signedIndexEquiv(ell).symm m`; use
`Equiv.apply_symm_apply` to identify the input alias with
`signedIndexEquiv(ell) k`, and unfold only this composite at the final
`change`.  This avoids dependent transport between the two coarse fibres and
keeps the only case split inside the already isolated natural quotient
theorem.

There is currently no direct coordinate-cast theorem for
`cmp99SourceAliasIndexOneReflection`; the sealed theorem is stated on the
explicit centered-vector subtype.  The next brick should first add the thin
depth-one corollary obtained from
`cmp99SourceFlatQprimeAliasIndexOneVectorEquiv_reflection` and
`cmp99SourceCenteredAliasVectorReflection_coordinate_cast_eq_neg`.  This is
transport through the sealed explicit bridge, not a new reflection law.  The
affine-carry theorem can then cite that corollary and stay at the literal
`CMP89Eq246AliasIndex d M 1` type consumed downstream.

4. Only then expose the commuting square and complete-sum reindexing of the
   conjugated equivalence.

The carry layer should be split into a natural-value theorem and its residue
corollary.  At one coordinate write

`k.val = ell.val + N' * q.val`.

Then periodic negation has target Euclidean quotient

`q'.val = if ell.val = 0 then ((M - q.val) % M) else M - q.val - 1`.

The zero branch deliberately retains `% M`: when `ell = 0` and `q = 0`, the
periodic negative is zero rather than the non-canonical value `M`.  The
consumer-facing statement should cast this equality to `ZMod M`:

`(q' : ZMod M) = -(q : ZMod M) - if ell.val = 0 then 0 else 1`.

Only after that theorem is established may the two sealed signed dictionaries
be used to derive

`cast (carry ell m) = - cast m + if ell.val = 0 then 0 else 1`.

This ordering keeps three logically different operations apart: canonical
periodic negation in `Fin (M * N')`, Euclidean borrow in the quotient `Fin M`,
and the extra negation already built into the signed CMP89 alias dictionary.
The final affine sign is otherwise very easy to reverse twice.

Static proof plan for the natural theorem (not compiler evidence):

- first expose `cmp99FinBoxFourierNeg` coordinate values with `ZMod.neg_val`;
- rewrite the source fine value by
  `cmp99SourceFlatQprimeFixedCoarseFibreEquiv_symm_apply_val`;
- split on `ell.val = 0`; only that branch splits again on `q.val = 0`,
  because periodic zero is the exceptional canonical representative;
- in the nonzero-residue branch rewrite
  `M*N' - (ell + N'*q)` as
  `(N' - ell) + N'*(M-q-1)` and use `ell < N'`, `q < M`;
- cast the result to `ZMod M` only after the natural quotient is fixed.

Definition-level audit sharpens the first step.  The target quotient is
literally `Fin.divNat`, hence division by `N'`, because
`finProdFinEquiv : Fin M × Fin N' ≃ Fin (M * N')` has inverse
`(x.divNat, x.modNat)`.  The most stable coordinate lemma should use
`ZMod.neg_val'`, not the piecewise `ZMod.neg_val`:

`(FourierNeg k mu).val = ((M * N') - (k mu).val) % (M * N')`.

This keeps the exceptional periodic zero in the outer remainder and postpones
the only genuine case split to the quotient theorem.  After substituting
`k.val = ell.val + N' * q.val`, the proof obligations are exactly:

- `ell.val = 0`: divide
  `((M*N' - N'*q.val) % (M*N'))` by `N'`, retaining `% M` when
  `q.val = 0`;
- `ell.val != 0`: rewrite the numerator as
  `(N' - ell.val) + N' * (M - q.val - 1)`, use
  `0 < N' - ell.val < N'`, then take the Euclidean quotient.

Do not unfold the conjugated signed dictionary while proving this arithmetic.
The natural quotient theorem should mention only `FourierNeg`, the two fixed
fibres and their literal `Fin.divNat` quotients.  The alias corollary is a
separate consumer, so a future change of centered representatives cannot
invalidate the Euclidean carry statement.

Recommended atomic split after the cross-fibre cold seal:

1. `BalabanCMP99SourceCoarseFibreFourierNegQuotientCarry`: only the
   coordinate value of periodic negation, the natural target-quotient formula
   and its `ZMod M` corollary (three audited declarations).
2. `BalabanCMP99SourceSignedAliasFourierNegCarry`: conjugate the already
   sealed signed fibre dictionaries through the cross-fibre equivalence,
   prove the commuting square, then derive the signed-alias affine residue
   law and complete-sum reindexing.

The first module must not import centered-alias reflection; its arithmetic is
independent of the carrier-algebra permutation from Step 8b.7.  The second may
import both, but it must not identify its new `ell`-dependent affine map with
`cmp99SourceAliasIndexOneReflection`.

No cancellation of `N'` inside `ZMod (M*N')` is permitted: that would erase
the Euclidean carry which this brick exists to expose.

Static preflight on the independent coarse-fibre checkpoint found one
definitional-type hazard before its first diagnostic.  The coordinate proof
of `cmp99SourceFlatQprimeCoarseAlias_fourierNeg` obtains periodic negation in
`ZMod (M * N')`, while its goal is in `ZMod N'`; these moduli cannot be
identified by `simpa`.  The faithful repair is to apply the canonical ring
homomorphism

`ZMod.castHom (dvd_mul_left N' M) (ZMod N')`

to the fine-modulus equality, then simplify only its action on negation and
natural casts.  This is reduction along the literal divisibility
`N' | M * N'`, not a new periodicity premise.  The source statement and the
cross-fibre scope stay unchanged; the old runner/blob hashes must be
superseded before any diagnostic rather than spending a session on the known
type mismatch.

Do not then assert simple intertwinement with
`cmp99SourceAliasIndexOneReflection`.  Euclidean division contributes a
coarse-residue-dependent borrow: for `M = 2`, `N' = 3`, `ell = 1`, `q = 0`,
the fine coordinate `1 mod 6` negates to `5 = 2 + 3 * 1`, so the target
quotient is `1`, not `-q = 0 mod 2`.  The correct target alias is therefore an
affine reflection with this carry.  The physical bridge must prove the full
coarse-plus-alias momentum identity and expose the carry explicitly; alias
reflection alone remains useful only as carrier algebra.

Scope gate: the first reflection brick ends at a genuine permutation of the
printed alias carrier, its residue law and alias-sum reindexing.  It does
**not** yet assert a physical-fibre permutation or that the amplitude
momentum, row coefficient or stabilized transpose solution equals a
column/endpoint object.  Those require the cross-fibre negation, period and
phase lemmas above; bundling them into the alias permutation would recreate
the orientation shortcut in a less visible place.

## Physical phase

Keep the character-to-endpoint-phase bridge separate from the row/column
coefficient reflection.  Gate 8 exposes
`cmp99FlatFourierMode k x * transposeSolution k`; the next statement must
prove the positive character equals the exact lattice endpoint phase at the
chosen sampled momentum/displacement.  It may not infer orientation from the
names `row` or `column`, and it may not identify a finite DFT sum with a
continuous Brillouin integral.

Available sealed ingredients are orientation-sensitive:

- `cmp99FlatFourierMode_eq_coordinateProduct` expands the positive character;
- `cmp99Flat_stdAddChar_eq_exp_discreteMomentum` converts each coordinate;
- `cmp99SourceFlatQprimeAmplitudeMomentum k = -M * discreteMomentum k`;
- `cmp99SourceFlatQprimeAmplitudeMomentum_eq_alias_add_period` transports that
  signed momentum to the literal CMP89 alias plus an exact `2*pi*M` period;
- `cmp89Eq251ComplexEndpointLatticePhaseFactor` uses the positive exponential
  of the endpoint displacement.

These facts do not by themselves choose the endpoint displacement or remove
the minus sign.  The residue reflection may reindex the complete fibre, but
the final phase equality still needs a named lattice-coordinate dictionary.
Do not absorb an `M` into the endpoint coordinate mentally: the exact fine vs
block unit conversion must be a theorem.

Static update after Step 8b.9: the source already contains the exact
cross-fibre momentum-period theorem
`cmp99SourceFlatQprimeAmplitudeMomentum_fourierNeg_eq_neg_add_period` and its
amplitude consumer
`cmp89Eq245EntireAverageAmplitude_amplitudeMomentum_fourierNeg_eq_neg` in
`BalabanCMP99SourceFlatWeightedAdjointFourierOrientation`.  Therefore Step
8b.10 must not reprove or weaken the momentum-period statement.  Its role is
only the affine alias-carrier action.  The later phase brick should combine:

1. the sealed Step-8b.10 reindexing candidate;
2. `cmp99FlatFourierMode_eq_coordinateProduct`;
3. `cmp99Flat_stdAddChar_eq_exp_discreteMomentum`;
4. the existing Fourier-negation momentum-period theorem above;
5. the exact integer-lattice period of the exponential phase.

The remaining dictionary is still the endpoint displacement/unit choice.
It must state which lattice displacement makes the positive DFT character
equal the `cmp89Eq251ComplexEndpointLatticePhaseFactor` numerator.  The
Holder normalization in that factor is not part of this phase identity and
must remain outside it.

## Order

1. cold-seal Gate 8;
2. materialize the mass-uniform complex-floor bridge;
3. construct and seal residue reflection plus physical-phase dictionary;
4. identify the finite sum with the sampled endpoint object;
5. only then address finite-grid periodization and the regional `B0` route.

## Mass-floor seal procedure

The current Colab diagnostic is pinned to source `733ecbb60...` and runner
vehicle `4161e239...`.  A PASS authorizes exactly one terminal cold workflow,
not another exploratory run.  The terminal vehicle must:

- checkout raw source `733ecbb60...`;
- gate the two Git blobs recorded above;
- run the focal and the three-declaration audit stop-on-first-error;
- reject new-module warnings and axioms outside the standard trio;
- record `cold=true` with project-graph restore and save both skipped.

Only that durable cold PASS may remove the two PRE-VALIDATION headers.  A
diagnostic PASS by itself changes neither source status nor the live counters.
