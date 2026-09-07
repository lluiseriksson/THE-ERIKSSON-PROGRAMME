# Point-source normalization: static route, not a compiler seal

The running FULL/mixed cold gate is independent of this note. No new Lean
claim, terminal field, inverse identity or window15 attainment is recorded.

## Reusable exact inputs inspected

- `cmp99Flat_normalizedCharacterAverage_integerResidue` in
  `BalabanCMP99FlatFiniteGridAliasing` is a normalized character sum over
  `ZMod N` in each coordinate. It selects a residue class, not equality of
  two arbitrary integer lattice sites.
- `cmp89Eq245CenteredAliasIntegers_eq_Ico` in
  `BalabanCMP89Eq245CenteredAliasCycle` identifies the printed alias set
  with N consecutive integers starting at `-floor(N/2)`.
- `cmp89Eq245CenteredAliasVectorPiEquiv` in
  `BalabanCMP89Eq245CenteredAliasVectorCycle` gives the actual product of
  these scalar fibres. It does not by itself identify this product with a
  finite Fourier character convention.

## Finite remaining normalization route

1. Reuse `cmp99SourceCenteredAliasResidueEquiv N` and its
   `_apply` theorem from `BalabanCMP99SourceCenteredAliasReflection`:
   the output is the literal integer cast, not an arbitrary enumeration.
   That module is already cold-verified at3bf925319be2b09c6d77706be64913e9817eb3b4.
   Lift coordinatewise through the existing centered-vector Pi equivalence;
   do not reconstruct the scalar equivalence from interval arithmetic.
2. Prove the character dictionary for the literal exponential alias phase;
   do not replace that phase by a ZMod character by definition.
3. Apply character orthogonality. The unnormalized alias sum contributes
   N^d when the integer displacement is divisible by N coordinatewise,
   and zero otherwise. This only selects congruence, not a point source.
4. On the divisible branch, use the remaining normalized Brillouin integral
   with integer displacement divided by N to select equality to zero.
   This is where the residue selector becomes the infinite-lattice delta.
5. Track the resulting N^d = xi^(-d), xi=1/N, against the separately
   specified counting/density normalization. Cancel that factor exactly
   once when constructing the actual physical action.

These are proof obligations, not proofs written or compiled in this note.
Step1's scalar input is already proved; only its required vector composition
and use in this normalization route are new work. This corrects the earlier
static list which unnecessarily proposed rebuilding the scalar reduction.
In particular the existing finite-grid aliasing theorem must not stand in
for step4: a congruence-class sum is not the infinite-lattice point-source
equation. No symmetry under negation of the even half-open alias set is
needed or assumed.

The alias fibre equation must use the mass-uniform solution-domain
producer already identified in the mixed-boundary map, rather than copying
an older mass-positive convenience theorem. The real/complex action
dictionary remains a separate visible obligation.

Counters: 20/41; TermSource=0; window15 open.

## Existing normalized-integral route inspected

The local Mathlib source was checked at the exact pinned commit
07642720480157414db592fa85b626dafb71355b. Its
`UnitAddTorus.orthonormal_mFourier` supplies normalized Haar character
orthogonality. The repository already supplies
`integral_unitAddTorus_eq_cmp89NormalizedBrillouin` for continuous torus
functions, and `cmp89UnitAddTorus_mFourier_neg_eq_exp_physicalPhase` fixes
the negative-momentum sign convention. These are candidates for step4,
not an invitation to introduce a second `(2*pi)^(-4)` factor.

The physical parameter uses the repository's centered/translated coordinate
dictionary; the remaining integer phase must be identified with that exact
torus character before transport. Neither ordinary uncentered Fourier
notation nor a finite-grid delta can replace this equality silently.
No new orthogonality proof or source equation was compiled in this audit.

`AddCircleMulti` uses a local normalized-Haar measure instance; the
repository's physical measure bridge names standard volume. Period one
makes them equal, but not a convention to erase silently. A Mathlib-only
PRE-VALIDATION repro now states the explicit period-one measure equality
and the four-dimensional character integral under product normalized Haar:
tmp/NeumannTorusCharacterIntegralRepro.lean. It is not yet compiled and is
not part of the live reindex cold queue. Only after this repro passes may
the exact physical phase dictionary consume its orthogonality conclusion.

## Coefficient roles in the later physical-action dictionary

Static reading of the actual source types, not a new compiler result:

- `cmp89Eq246EntireAliasPrecisionMatrix` uses its parameter `a` literally
  as the coefficient of the rank-one averaging column/row product.
- `cmp85SourcePrefixA (M := M) a r` instead computes the prefix coefficient
  from the initial parameter: `cmp99SourceMassParameter a M (r.val - 1)`.
- `cmp85SourcePrefixWeightedCoefficient T a r` multiplies that prefix
  coefficient by `terminalSpacing^(-2)`.
- `cmp85SourcePrefixCountingCoefficient T a r` further multiplies by
  `terminalSpacing^d / spacing^d`, to convert the weighted adjoint to the
  counting-Hilbert adjoint used in Lean.
- `neumannCanonicalPrecision_apply_eq_completeOffsets` keeps the literal
  counting coefficient multiplied by the averaging weight to power
  `2*(steps+1)`. The complete fibre is not silently renormalized there.

Consequently the later dictionary must instantiate the Fourier coefficient
with the actual effective prefix coefficient, rather than identifying two
parameters both named `a`. At a normalized terminal spacing of one, the
intended Fourier coefficient is `cmp85SourcePrefixA`; the preceding scale
normalization and its index shift must remain explicit. The remaining
volume ratio cancels one of the two counting weights, leaving one normalized
fibre average. This cancellation is ALREADY cold-sealed in
`NeumannCanonicalSpacingNormalization`, source
dd9354a87d2e9d60dac69aa79f287b53e45ba207, ledger1164:

- `neumannCanonicalFourierSpacing_terminal_eq_one` derives terminal spacing1;
- `neumannCanonicalFourierSpacing_countingCoefficient` gives a_r*B^d;
- `neumannCanonicalFourierSpacing_countingMassCoefficient` combines the
  two counting weights to obtain a_r*B^(-d) exactly.

Reuse these named theorems. The initial audit above identified the correct
convention but unnecessarily treated the scalar equality as remaining work;
the follow-up declaration check removes that duplicate debt. It is not a
new premise or an invitation to cancel the fine-density point-source factor
twice.

What remains is consumption of these scalar producers inside the action
dictionary, not reproving their algebra. The
current mixed Green seam theorem intentionally leaves its coefficient
parameter explicit and does not claim to instantiate the canonical tower.
