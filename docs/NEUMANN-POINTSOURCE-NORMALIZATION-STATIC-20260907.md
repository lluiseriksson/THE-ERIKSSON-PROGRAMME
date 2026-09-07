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

## Complex-to-real action boundary (static audit)

The canonical precision acts on real Lie coordinates; the physical Fourier
Green series is complex-valued. The intended bridge is to prove the literal
complex source equation first and then take its real part, not to assume
that the complex kernel is real. Real coefficients commute with real-part
projection in the finite action. For the infinite image series this step
must consume the actual mixed-series summability theorem.

Pinned Mathlib provides `Complex.re_tsum` in
`Mathlib/Analysis/Complex/Basic.lean`, with an explicit `Summable` premise;
equivalently use `Complex.reCLM.map_tsum`. This checks the available generic
transport, not the still-open physical source equation or inverse identity.

Do not substitute the older
`BalabanCMP89NeumannPhysicalRealReflectionSummability` specialization:
it belongs to the withdrawn Eq248 scalar one-displacement route, not this
Eq246 mixed physical kernel. No new compiler evidence or terminal field is
claimed by this interface audit.

## Literal Brillouin phase specialization prepared

`tmp/NeumannPhysicalBrillouinCharacterDraft.lean` now consumes the named
period-one volume/Haar equality, the sealed normalized-measure transport,
and `cmp89Eq248NegativeTwoPiTorusMomentum_physicalBrillouin` to state
orthogonality for the actual parameter `cmp89Eq251PhysicalBrillouinParameter`.
The integer phase uses `mFourier (-u)` with the source's translated momentum;
no parity convention or extra `(2*pi)^(-4)` is introduced.

This is PRE-VALIDATION, text guard only. It is not in the live cold queue
or the separately prepared masked-difference HOT queue. Its three goals
are volume character integral, literal physical phase identity, and normalized
physical integer-character integral. Even a future PASS would leave the
alias-weighted fine source equation and finite action interchange open.

The companion PRE-VALIDATION `tmp/NeumannAliasPrecisionReadoutDraft.lean`
applies the literal target-phase sum to the already constructed Eq246 solver
equation. It accepts only the named nonvanishing domain, not a source or
solution family; the physical specialization must use the existing
mass-uniform domain producer, not reinstate mass>0. Combining endpoint phases
is valid here AFTER precision application. It is not a replacement of the
two-endpoint Green by the withdrawn one-displacement Eq248 kernel.
This draft has passed only the text guard, not Lean, and is outside both
queues currently fixed. The next composition still needs the exact alias
sum, normalized physical character integral and actual finite action.

## Orientation of the pending averaging-action dictionary

Static derivation from the literal definitions, NOT compiler evidence:
`cmp89Eq245EntireAverageBase N q = exp(-i*q/N)`; hence the column `u(q)`
contains negative offset phases, while the row `u(-q)` contains positive
offset phases. The inverse-transform target wave is positive. Therefore
the average over targets `N*k+r` must consume the ROW, not the column.

For an integer owner k and offsets0<=r<N in every coordinate, the two
identities to prove and then compose are:

- Normalized complete-fibre average of exp(i*(z+2*pi*m)*(N*k+r)/N)
  equals exp(i*z*k) times u(-(z+2*pi*m)). Integer alias phase at the owner
  must be removed by its named lattice-period lemma, not by a symmetry claim.
- Sum over centered aliases of exp(i*(z+2*pi*m)*x/N) times u(z+2*pi*m)
  equals exp(i*z*k) when x=N*k+r. Expanding u produces N^(-d); the alias
  character sum produces N^d only for the matching offset r. These cancel
  exactly once. This is synthesis of a block-constant field, not a factor
  to hide in the scalar coefficient.

These formulas describe the complex plane-wave action; the actual canonical
operator still needs the complete-offset equivalence and the already sealed
counting coefficient identity. N=L^j on the Fourier side must be explicitly
identified with the generated terminal block side, rather than identifying
parameters merely because both describe a scale. No new uniform bound,
physical inverse or terminal-field producer is claimed here.

## Density kernel versus counting inverse

The literal `cmp89Eq246NormalizedPhysicalFineToFineGreen` is only the
normalized Brillouin integral of the full alias integrand: its definition
does NOT insert an additional fine-cell volume. Its source is the density
delta `xi^(-d) * delta`, as fixed by
`cmp89Eq243NormalizedFinePointSource`. Consequently the pending counting
inverse must multiply that density kernel by `xi^d` exactly once; this is
separate from the already sealed cancellation inside the Qprime mass term.
Expected future action: A(G_density) = xi^(-d)*delta, then
A(xi^d*G_density) = delta. Neither equation is proved by this static note.
An inverse criterion requiring a counting point source must not consume
the unscaled density kernel merely because its name says normalized.

## Exact remaining congruence-to-delta composition

The prepared exponential selector draft keeps the positive phase and factors
out exp(i*sum(z_i*u_i/N)); it does not identify congruence with equality.
For the forthcoming four-dimensional integral, split on the literal vector
of integer casts into ZMod N. On its nonzero branch the finite sum is zero.
On its zero branch `ZMod.intCast_zmod_eq_zero_iff_dvd` supplies N divides
each u_i; use the explicit quotient u_i/N and `Int.ediv_mul_cancel` to
identify the remaining phase with the physical integer character. N is
nonzero, so that quotient vector is zero exactly when u is zero.
The endpoint is N^4*delta(u), not delta(u). The xi^4 counting-kernel factor
is consumed only afterwards, as recorded above.

The normalized Brillouin integral definition is a fixed complex scalar
times a Bochner integral over the translated cube. `integral_mul_const`
therefore transports the finite selector's constant factor without assuming
integrability of a new arbitrary family; the actual pointwise phase identity
is still required. No second (2*pi)^(-4) enters. This route is inspected
against the pinned Mathlib and source definitions, not yet compiled.

## Laplacian action: reuse boundary masks, not discrete momentum restriction

`cmp99FlatPeriodicComplexStencil_fourierMode` is an exact finite ZMod-mode
identity, but its momentum is discrete. The physical Brillouin variable is
continuous, so this theorem is not the missing action dictionary by itself.
The literal alias diagonal is `cmp89Eq245EntireScaledLaplacianSymbol`:
sum of D_xi(q)*D_xi(-q), plus mass squared, with
D_xi(q)=(exp(-i*xi*q)-1)/xi. Its integer-shift stencil factor must therefore
be proved as (2-exp(i*xi*q)-exp(-i*xi*q))/xi^2, using the opposite exponential
product identity, before summing coordinates. No real-slice conjugation is
needed for that algebraic identity.

The physical finite stencil is already named in
`neumannFlatInternalBond_laplacian_apply`, with two explicit spacing inverses
and separate outgoing/incoming masks. HOT1229 supplies the generic masked
endpoint identities; the physical FULL/PROPER seam producers must discharge
their hypotheses for the mixed series. Do not apply periodic wrap to an
individual continuous-momentum phase: the relevant periodicity belongs to
the constructed image sum. The operator/image interchange remains a later,
summability-dependent step. This is a static route, not a new action proof.

## Image delta collapse: use the varying-source family

After operator/image interchange, a counting delta must select exactly the
original source inside the half-open rectangle. Fixed-source injectivity
alone does not exclude another source's image from that rectangle.
The stronger sealed `neumannMixedCoordinateImage_bijective` already varies
both the original interval point and its image index. Compare any image
equal to an interior target with the target's zero-translation, unreflected
representative. Its injective component then identifies both the original
source and the image index. FULL has translation alone; PROPER uses the
unreflected branch at zero. Coordinatewise assembly gives the corresponding
unique tensor representative, without a new geometric counting bound.

This is an inspected proof route, not a compiled delta-sum theorem. The
zero-representative evaluation, dependent index equality and final singleton
tsum still need explicit lemmas. It does not discharge the physical operator
action or its interchange with the image series.
