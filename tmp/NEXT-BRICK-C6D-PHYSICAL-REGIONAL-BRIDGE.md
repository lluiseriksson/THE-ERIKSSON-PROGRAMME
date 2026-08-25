# C6d static boundary: literal source-flow flat B0 to regional CMP99 (3.42)

Status after the first gate: the uniform ambient point-source and
localized-field queue stopped at its first focal.  The executed source was
`f681aacdeab3be53ccb0abb70c93493236515323` and the executed runner was
`59b2ddf5a34d4cd52dc54a617b53975124ca45f6`.  Lean reported only two
positivity failures in
`BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0.lean`
at `47:4` and `85:40`; no audit or localized-field target ran.  Therefore no
PRE-VALIDATION mark is retired and no theorem is claimed.

The corrected source checkpoint is
`73bb1a2008c557840a91e50d8abe6b874947f7ee`; the retry runner checkpoint is
`a754e28555270ebbdab8bff05f262368a39c43fa`, with runner SHA-256
`2563BFBA3DE16B09733D2AE751A7F39ED0D29282386857EF51F8ED0767A29021`.
The fast-forward push succeeded on 2026-08-24 and the remote branch was
verified at `a754e28555270ebbdab8bff05f262368a39c43fa`.  One Colab Pro+ CPU / high
RAM retry ran in `Untitled207.ipynb` from source
`73bb1a2008c557840a91e50d8abe6b874947f7ee`.  Its launcher hash gate printed
the expected
`2563bfba3de16b09733d2ae751a7f39ed0d29282386857ef51f8ed0767a29021`,
`RUNNER_REV=source-flow-uniform-point-source-b0-v3`, `RAM_GIB=50.99`, and the
exact source blob hashes before entering `cache_get`.  The cell was launched
once, but its frontend disconnected during the focal.  The runtime later
unassigned; the durable notebook stops at the focal `CMD`, with no `EXIT`, no
`FINAL_STATUS`, and no matching local archive.  It is therefore classified
`INCOMPLETE-RUNTIME-LOSS`, not PASS or FAIL, and all four PRE-VALIDATION marks
remain.

A single durable cold GitHub terminal gate for the same immutable source is
prepared locally at control commit
`ebccd7e8811d639587563fe060705811163e1c57`.  It verifies all four source blob
hashes, runs the uniform focal/audit followed by the localized focal/audit
stop-on-first-error, gates exactly five plus two axiom blocks, and uploads an
artifact even on failure.  It has not been pushed or dispatched: the required
preflight stopped because `gh auth status` reported the `lluiseriksson` token
invalid and Git HTTPS returned `Failed to connect to github.com port 443`.
No fallback, force-push, workflow dispatch, local Lean/Lake or second Colab
run was attempted.

The fail-closed recovery command is prepared and PowerShell-parse checked:

```text
5EE72D9E479785911FD3D6BCCD06FB8715FEC0E2FAA95D5C03EDFCC15CA51079
  tmp/push_and_dispatch_uniform_b0_terminal.ps1
```

It requires the exact local/control SHA, accepts only the known remote parent
or the already-published control SHA, proves fast-forward ancestry before the
push, verifies the remote head, refuses a second dispatch for the same head,
and then launches exactly one cold terminal workflow.  It must not be run
until `gh` again authenticates as `lluiseriksson`.

The owner subsequently published and re-verified the retry control
`a754e28555270ebbdab8bff05f262368a39c43fa`; this does not publish the
terminal control commit.  The local branch remains exactly one commit ahead
at `ebccd7e8811d639587563fe060705811163e1c57`, with the large unrelated
untracked worktree preserved.  No terminal workflow has yet been dispatched
for that SHA.

The terminal evidence retrieval boundary is now also prepared and tested
without network or Lean:

```text
6D6A6082DC81184C86E18D3F1E96C5279541CE40EFE219975FBE04F2FF05203D
  tmp/audit_uniform_localized_b0_terminal_evidence.py
41239055ECD306BE864C2DED6D4F0D95B6D42B0D3B994AE210F1CE2DF47AE1C8
  tmp/test_uniform_localized_b0_terminal_evidence.py
BF6151533D98C35461C46D9498A12DB367D2998C0E81AFAF6EE8EAC06ADD211B
  tmp/retrieve_uniform_localized_b0_terminal_evidence.ps1
```

The synthetic self-test prints
`UNIFORM_LOCALIZED_B0_TERMINAL_EVIDENCE_SELFTEST_OK` and proves both a PASS
fixture and fail-closed rejection after tampering with `FINAL_STATUS`.  The
retriever selects exactly one workflow run by the exact control SHA, downloads
both the raw GitHub ZIP and its extracted artifact, and accepts it only after
checking the four zero exits, five plus two measured axiom blocks, exact
source/control/toolchain/Mathlib pins, `SHA256SUMS`, the deterministic inner
archive digest, and byte equality of both archive layers.  A GitHub run summary
alone is never evidence for this gate.

## Fixed input after the current gate

The verified endpoint, if the gate passes, controls only

`G_flat Q'^* : coarse source field -> ambient fine zero-cochain`

with one `rho > 0` and one `B0 > 0` uniform in `depth`.  The arbitrary source
field is supported at one literal source owner and the estimate has no source
cardinality factor.  It is complex, ambient and flat; it is not the regional
Dirichlet Green and gives none of the three derivative actions in (3.42).

## Finite source-faithful chain

1. **CMP99 (3.35) local representative.** Promote the literal ordinary
   forward derivative and the cube-local regularity witness.  The gauge stays
   local; no global gauge identity is assumed.  The witness is a cited source
   output, not a supplied perturbation norm or Green estimate.
2. **Exact read carrier.** Determine the minimal background carrier of the
   regional covariant Laplacian and discharge its inclusion from the printed
   `Omega'_0 subset square` dictionary.  The canonical identity extension is
   only an implementation device; operator equality must be a theorem on the
   actual read carrier.
3. **Literal interacting precision.** Construct the regional/ambient
   `Delta'_a = Delta_U + Q'^* a Q'` using the retained physical tower.
   Identify the exact `Q'` by the terminal tower theorem.  Do not use the
   generated coefficient and do not accept `SmallBackgroundPerturbation`.
4. **Printed perturbation factorization.** Derive the difference from the
   exponential representative using the literal CMP99 (3.61)--(3.63)
   algebra, including the exact three-term `Q'^* a Q'` contribution.  The
   `O(alpha1)` weighted owner bound must be produced from the (3.35) amplitude
   and forward-derivative bounds; it cannot be an input named after the
   desired estimate.
5. **Dirichlet compression and resolvent.** Compress both literal precisions
   to the same active region, prove the compressed perturbation identity, and
   construct the interacting inverse by the first/second resolvent identity
   from the flat inverse.  The relative weighted norm `< 1` is an attained
   scalar theorem, not a free hypothesis.  Use the uniform ambient `B0,rho`
   once; no depth-dependent CT/Poincare coefficient may replace it.
6. **Four physical actions.** Build value, left derivative, right adjoint
   derivative and Laplacian estimates for the same canonical regional Green.
   Derivative spacing is literally `L^(depth+1) * spacing`; operator
   identities precede estimates.  Combine their amplitudes with
   `cmp99Eq342CommonAmplitude` only after each action is constructed.
7. **Uniform certificate.** Produce one
   `CMP99Eq342SourceLocalizedGreenCertificate` with `B0,delta0` independent
   of depth.  Nonempty regional carrier must be derived from the physical
   root/index, not assumed for an arbitrary region.
8. **Window 15.** Feed the certificate into the direct CMP99 (3.89)
   correction estimate.  The `K^-1` gain enters before owner/layer summation,
   overlap remains the single source `16`, and the weighted owner norm is
   used instead of the sealed generated CT+Schur budget ruled out at depth
   zero.  Only a proved `norm R' < 1` marks window 15 attained.

## Static contract for step 3

The first exact-read implementation proves a sufficient one-bond-collar
locality theorem by identifying the covariant derivative before forming
`D^*D`.  Static composition shows that this sufficient carrier is too strong
for the printed dictionary: `Omega'_0 subset square` does not imply that the
exterior one-bond collar is also contained in the square, and the retained
average carrier cannot supply the missing implication (at depth zero its
carrier is empty).

The expected source-faithful repair is sharper rather than stronger.  In the
quadratic form of the zero-extended Laplacian, a boundary edge with only one
endpoint in `Omega` contributes the norm square of the interior field; the
background action cancels by the isometry of the adjoint representation.
Only bonds with both endpoints in `Omega` should therefore require equality
of backgrounds.  Since `Omega = Omega'_0` and `Omega'_0 subset square`, that
minimal internal-bond carrier is discharged by the printed dictionary.  This
boundary-cancellation theorem must be proved and audited before step 3 may be
called source-closed.  The currently compiling prefix remains useful
infrastructure but does not, by itself, establish this sharper equality.

Scope gate: boundary cancellation proves equality of derivative **norms**
for every zero-extended field, hence equality of the symmetric quadratic
forms and of `D^*D`.  It does not prove equality of the covariant derivatives
themselves: on an inward boundary edge the two outputs may differ by distinct
isometric background actions.  The promoted theorem must therefore end at
the regional Laplacian.  Any later consumer needing literal derivative
equality must return to the stronger one-bond-collar carrier rather than cite
the internal-bond theorem.

The exact-read-carrier prefix returns a
`CMP99SourceLocalizedRetainedTower`.  It must not be coerced into
`CMP99SourceRetainedPhysicalScaleIdentification`: the latter is indexed by
the canonical iterated-lift lattice family and a full scaled stratification,
whereas the source-region endpoint carries an arbitrary typed active-region
chain.  Treating those two families as definitionally identical would add a
false dictionary.

The required literal operator already has the correct generic constructor:

```text
cmp99SourceGaugePrecision
  (cmp99ActiveRegionSourceCovariantLaplacian
    Omega rho transformedBackground spacing)
  ((localizedTowerAt (Fin.last depth)).Qprime)
  a_j
```

Thus the step-3 source endpoint must:

1. construct the localized retained tower internally from the (3.35)
   regularity class, selected cube, source-region dictionary and scalar
   regime;
2. use the original transformed background in the literal regional
   Laplacian, not the canonical identity extension outside the read carrier,
   and fix its derivative spacing to the same source `eta` rather than expose
   a second free scalar;
3. expose the definitionally literal decomposition
   `Delta_U + a_j * Q'^* Q'`;
4. prove equality with the canonical-terminal presentation by the named
   `CMP99SourceLocalizedRetainedTower.terminalQprime_eq`; and
5. derive symmetry and the exact quadratic form from the already proved
   generic theorems, without accepting a precision, a `Qprime`, a coercivity
   estimate or a Green operator from the caller.

The exact six-file PRE-VALIDATION scratch package is
`tmp/C6D-STEP3-LOCALIZED-PRECISION-DRAFT-PATHS.txt`.  Its final source-facing
wrapper now fixes the regional covariant derivative spacing to the same
printed `eta`; it does not expose the formerly independent `spacing` scalar.
The reusable leaf remains parameterized by an `SUNAdjointModel`, while the
source equality fixes that parameter to the canonical
`matrixSUNAdjointModel Nc`; no source conclusion is obtained from a
caller-selected action.
The read-only promotion and materialization previews both report six files,
eleven declarations/readouts and promoted-manifest SHA-256
`2BECC005430EE05217A39AD08CF127DE9B3519095E26836CB4CC5D718908DFD7`.
All text/import/readout gates pass, but the files remain scratch-only and have
no compiler or axiom-oracle verdict until the preceding C6d boundary seals.

The coefficient `a_j` remains the printed flowing scalar parameter.  This
brick neither manufactures its positivity nor replaces it by a generated
coefficient.  Coercivity, inversion and the attained relative-norm gate
belong to steps 4--5, not to the literal-construction brick.

## Static contract for step 4

CMP99 (3.53), (3.59) and (3.60) fix the real-slice algebra before any
estimate.  With

```text
Delta1 = Delta0 - V1,
Q1 = Q0 + F2,
```

the literal perturbation is

```text
V' = V1
   - a F2^* Q0
   - a Q0^* F2
   - a F2^* F2,
```

and hence `K1 = K0 - V'`.  The three averaging terms must stay separate in
the public definition: no shared norm budget is allowed to replace their
operator identity.  The factorization (3.62) is then obtained only after a
right inverse `G0` of the unperturbed precision has been constructed:

```text
K1 = (I - V' G0) K0.
```

The current two-file scratch boundary is
`tmp/C6D-STEP4-EQ360-PERTURBATION-DRAFT-PATHS.txt`.  It defines exactly this
real-Hilbert perturbation and the factorization theorem, with no inverse or
smallness premise hidden in the definition.  Both repository lightweight
guards pass (`LEAN_OVERLAY_TEXT_OK files=2` and
`LEAN_IMPORT_PREFIX_OK files=2`), but no `.olean` or axiom verdict exists.
The scratch audit now also carries the required visible PRE-VALIDATION mark;
this is governance metadata only and does not promote or validate the brick.

This is deliberately a **real-slice** brick.  The printed source warns that
the analytically continued `F'_2*(A)` is not the Hilbert adjoint of
`F'_2(A)` away from the real slice.  A later complexification dictionary must
therefore construct the starred analytic coefficient independently; this
scratch theorem must not be reused as that missing identification.

There is a second, independent dictionary boundary at (3.59).  The sealed
`terminalQprime_eq` family compares a localized retained tower with its
canonical extension **for the same physical background**.  It is not the
printed comparison

```text
Q'(U'U) = Q'(U) + F'_2(A).
```

The source-specific step 4 must therefore construct two towers on the same
typed regional spaces: `Q0` from the regular baseline background `U` (or its
proved gauge-equivalent local representative), and `Q1` from the
**multiplicatively perturbed** background `U'U`.  Only then may it define the
real-slice `F2 := Q1 - Q0` and discharge (3.59) definitionally.  Reusing the
localized-versus-canonical terminal equality as (3.59), or accepting `F2`
without those two physical towers, is rejected.

This statement splits at the real/complex frontier.  The existing
`CMP99SourceWeightedRegionalTower.step` requires each transport to be a real
linear isometry `g ≃ₗᵢ[ℝ] g`; it is valid for the compact `SU(N)` real slice.
Conjugation by the `SL(N,C)` background produced from complex `A'` is not
unitary and cannot inhabit that transport type.  Consequently the analytic
continuation of `Q'(U'U)` needs a separate complex-linear averaging recursion,
and the printed starred coefficient must be constructed as its analytic
synthesis rather than Lean's Hilbert adjoint.  Coercing the complex transport
to an isometry, or reusing `.adjoint` away from the real slice, is rejected.
This is the type-level form of the printed warning that `F'_2*(A)` is not the
Hilbert adjoint of `F'_2(A)` after complexification.

The perturbation field `A` in Section B, defined by `U' = exp(i eta A)` in
(3.37), is not the logarithmic representative used earlier to gauge-fix the
regular baseline `U` on a source cube.  The step-3
`localizedRetainedPhysicalPrecision_eq_exponentialSource` theorem isolates
that earlier baseline gauge representation; it does not construct `U'U`,
`V'_1(A)` or `F'_2(A)`.  Those are separate source-specific producers for
step 4.

There is also a gauge-covariance dictionary between those two layers.  The
printed (3.37) perturbs the original regular background `U`, whereas the
step-3 regional precision is expressed in the cube's gauge-transformed
representative.  A source wrapper must therefore either build both towers
before transport and conjugate them together, or construct the transported
field `R(u)A'` and prove the literal matrix identity

```text
exp(i eta R(u)A') U^u = (exp(i eta A') U)^u.
```

Applying the untransported perturbation `A'` directly to the transformed
background is a different configuration and is rejected.  The two-file
PRE-VALIDATION boundary
`tmp/C6D-STEP4-EQ337-COMPLEX-GAUGE-COVARIANCE-DRAFT-PATHS.txt` now constructs
the transported one-cochain and states the positive-bond matrix identity.
It is uncompiled and remains a gate before the two-tower producer.

The corresponding real-domain transport is now a separate two-file
PRE-VALIDATION boundary,
`tmp/C6D-STEP4-EQ337-REAL-GAUGE-COVARIANCE-DRAFT-PATHS.txt`.  It fixes the
source-vertex action to `matrixSUNAdjointModel`, derives the complete
`(mu,nu)` tensor covariance from `SUNAdjointModel.ad_mul` and inverse
cancellation, and constructs the transported (3.37) domain witness from the
original one.  Thus neither the transformed amplitude bound nor the
transformed covariant-derivative bound is a new caller hypothesis.  The
source/audit/path-list SHA-256 values are respectively
`BFBF883A35F637568EA78A06BAA2DF890AD8FAEB34BA441A30FB7B1AE69F2A36`,
`0B6356476A0D1D7C2FDF67E7B10D9B881AF425E28523BB838875E22672E936D1`,
and
`2D086C9EBF05AE9FE8ACAD53E6A04B326E8B86EC7A2B9BD522943D92C96B37B0`.
The lightweight text/import/readout gates pass at `2/2` and `6/6`, but no
compiler verdict exists and the boundary is not appended to the C6d gate in
flight.

The multiplicatively perturbed background itself is already a literal object
in the tree:

```text
cmp98PhysicalSuLeftVariation U A eta
```

whose positive-bond value is `cmp98PhysicalSuIncrement A b eta * U b`.
Step 4 must reuse that definition rather than introduce a free `U1` or a new
chart convention.  The generic scratch perturbation now determines
`F2 := Q1 - Q0` internally from its two operator arguments; its future
source wrapper must construct those arguments from `U` and this exact
perturbed background.

Visual source check of CMP99 printed p. 396 fixes the perturbation domain
without the OCR corruption previously visible in extracted text.  Equation
(3.37) reads, for every `j = 0,...,k` on `Omega_j`,

```text
|A'| < alpha1 (L^j eta)^-1,
|nabla^eta_U A'| < alpha1 (L^j eta)^-2.
```

There is no factor `2d` in the second inequality.  Moreover `A'` is valued in
the complexified Lie algebra in the printed analytic theorem.  The real-slice
producer may specialize this datum to a physical one-cochain, but the later
holomorphic producer must retain the complex type and the covariant
derivative; neither bound may be replaced by an unstructured sup-norm input.
Both source-facing scratch domains now fix the adjoint action internally to
`matrixSUNAdjointModel`; only the leaf derivative constructor remains generic.
Thus a caller cannot satisfy (3.37) by choosing a different orthogonal model.
The render hash and exact transcription are recorded in
`tmp/CMP99-EQ337-SOURCE-CARD.md`.

The apparent conflict with the earlier C6c.8f0a retraction is now resolved
at source level.  The retraction remains correct for (3.35), whose derivative
is ordinary and background-free.  But (3.37) explicitly prints
`nabla_U^eta A'`, and p. 397, (3.39), identifies its norm with the complete
covariant tensor `(D^U_mu A'_nu)(x)`.  Therefore the valid algebraic core has
been copied, not resurrected in place, into the two-file scratch boundary
`tmp/C6D-STEP4-EQ337-REAL-COVARIANT-DERIVATIVE-DRAFT-PATHS.txt`.  It fixes the
orientation of (3.3), constructs the real-slice tensor internally and leaves
the complexified producer explicit.  It is PRE-VALIDATION and cannot yet
discharge item 2 below.

The real-slice source domain is also now explicit in scratch.  The four-file
boundary `tmp/C6D-STEP4-EQ337-REAL-DOMAIN-DRAFT-PATHS.txt` stores one
fine-lattice perturbation field and quantifies its two bounds over
`S.global.regions r.castSucc` for every `r : Fin n`.  Its majorants are
literally `alpha1 * (L^r * eta)^-1` and
`alpha1 * ((L^r * eta)^-1)^2`.  It does not replace those regions by the
coarsened `CMP99SourceActiveRegionChain`, accept a free family of fields, or
claim the complexified domain.  Its explicit `[NeZero n]` gate prevents the
all-scales requirement from becoming vacuous.  Textual guards pass; no
compiler verdict exists.

The finite source-specific chain from the step-3 baseline to (3.60) is now:

1. reuse `cmp98PhysicalSuLeftVariation U A eta` for `U'U`;
2. encode the two literal (3.37) bounds on the active-region chain, first on
   the physical real slice and later in the complexified fibre;
3. derive retained-read-carrier near-identity for `U'U` from the baseline
   bound and the exponential increment, exposing the enlarged scalar radius;
4. construct the baseline and perturbed localized towers on the same typed
   regional chain and define `F2 := Q1 - Q0` internally;
5. expand the covariant Laplacian difference into the local `V'_1(A)` of
   (3.51)--(3.54), rather than merely renaming `Delta0 - Delta1`;
6. assemble the four-term `V'(A)` and prove (3.60) using the generic
   real-slice algebra brick; and
7. prove the literal local estimate (3.61), then compose once with the
   already produced baseline Green to obtain (3.63).

The present generic two-file scratch boundary covers only the algebra in item
6 (with `F2` computed from `Q0,Q1`) and the formal factorization underlying
(3.62).  It is not a producer for items 2--5 or either analytic bound.

A second two-file leaf boundary,
`tmp/C6D-STEP4-EQ337-NEAR-IDENTITY-DRAFT-PATHS.txt`, now implements the
quantitative product step needed inside item 3:

```text
norm (exp(eta A_b) U_b - 1) <= 2 (|eta| rA) + rU.
```

It uses the literal `cmp98PhysicalSuLeftVariation`, the sealed exponential
deviation estimate and the exact two-factor `SUN` telescoping inequality.
Both lightweight guards pass.  It remains PRE-VALIDATION and deliberately
does not claim the scale-indexed (3.37) producer for `rA`.

The amplitude half of that connection is now explicit in the eight-file
scratch closure
`tmp/C6D-STEP4-EQ337-REAL-NEAR-IDENTITY-DRAFT-PATHS.txt`.  At a fixed source
scale it derives the matrix generator radius from the literal (3.37) domain
and feeds the product lemma for `cmp98PhysicalSuLeftVariation`.  The baseline
radius and the scalar condition
`alpha1 <= 1/2` remain named inputs.  The spacing cancellation
`|eta| * alpha1 * (L^r * eta)^-1 <= alpha1` is proved internally for every
scale, so no free `hsmall` survives.  Thus this is a real-slice reduction,
not yet a discharge of the source alpha-window or a complex analytic
producer.  Textual guards pass; no compiler verdict exists.

The real perturbed retained-tower boundary is now explicit in the separate
two-file PRE-VALIDATION manifest
`tmp/C6D-STEP4-EQ337-PERTURBED-RETAINED-TOWER-DRAFT-PATHS.txt`.  It first
proves that both strata supporting a regular cube lie in the corresponding
source region, transports the literal (3.37) datum through the constructed
source-vertex gauge action, and derives the retained-read bound
`norm (exp(eta A') U - 1) <= 4 alpha1`.  It then constructs the perturbed
localized retained tower from `cmp98PhysicalSuLeftVariation`, fixing its
lattice spacing to the same source `eta`; no free spacing, `Q1`, `F2`,
precision, Green operator or operator identity is accepted.  The
source `Ubar` radius chain, source-region dictionary and scalar alpha window
remain visible inputs, so this is only the real item-4 construction boundary,
not the analytic complex tower or an attainment result.  The source, audit
and manifest SHA-256 values are respectively
`73714BF7D3697E3D2EACC6640B1831BEBAD834B49CF9459F51BC57D49EF63548`,
`EF805C112C3C01E2E00188B5D0FB549A0ACE756FAA4901A6A491A1E44CE50CDC`
and
`FC3C704EEE907C5AF1BD514293ACDFC76FC3DC6B8080B11BA24B0F1F4DFED660`.
The lightweight text/import/readout gates pass at `2/2` and `4/4`; no
compiler or axiom-oracle verdict exists and this boundary is not part of the
C6d run already in flight.

The complex half is no longer represented by an arbitrary derivative input.
The eight-file scratch closure
`tmp/C6D-STEP4-EQ337-COMPLEX-DOMAIN-DRAFT-PATHS.txt` extends the compact
background's adjoint action complex-linearly on the explicit
`SUNLieComplexCoord` fibre, constructs the full `(mu,nu)` tensor with the
source orientation, and states both (3.37) bounds on the same nonterminal
fine regions.  The action is theorem-proved to agree with the real physical
adjoint action on the real slice, and the complete derivative tensor is
theorem-proved to restrict to the real tensor under coordinatewise
complexification.  The complex exponential background
`exp(i eta A') U`, its localized averages and its analytic estimates remain
open.  Textual guards pass; no compiler verdict exists.

The complete real/complex (3.37) scratch frontier is the ordered sixteen-path
manifest `tmp/C6D-STEP4-EQ337-PHYSICAL-DOMAIN-DRAFT-PATHS.txt`; the existing
name is retained to avoid creating a second competing frontier.  At the current
bytes its SHA-256 is
`DF99D6FD0415A2E7EC44F4E661BABAEEE7644D4A23885286AC821001A2271088`, and both
lightweight gates report `files=16`.  It is a
future focal boundary only: it has not been materialized, promoted, built or
audited, and it must not be appended to the Colab gate already in flight.
The audit surface is now total at the textual level: all 58 public
definitions/theorems/structures have exactly one matching `#print axioms`
readout (58/58, including public aliases, with no unknown readout).  This is
still only a scope gate; none of those readouts has been executed.

The next source dictionary is now written as the two-file PRE-VALIDATION
boundary
`tmp/C6D-STEP4-EQ337-COMPLEX-PERTURBED-BACKGROUND-DRAFT-PATHS.txt`.  It
constructs the complex-linear matrix realization of `SUNLieComplexCoord`,
keeps the printed Hermitian convention as an explicit `1/i` normalization,
forms the literal positive-bond matrix `exp(i eta A') U`, and theorem-proves
that its real slice agrees with `cmp98PhysicalSuLeftVariation`.  This is not
yet a compiler-verified dictionary.  Tracelessness and determinant one are
kept as named theorems, so the positive bonds are packaged in `SL(N,C)` and
the full oriented background is reconstructed canonically.  Localized
averages, the two retained towers and their analytic estimates remain open.
A free complex background, or an asserted real-slice equality, is rejected
as a substitute.

### Finite contract for the analytic complex tower

The complex continuation is a separate finite construction, not a coercion
of `CMP99SourceWeightedRegionalTower`.  Its next boundary is fixed as the
following ordered list.

0. **Complex coordinate equivalence.**  Upgrade
   `cmp99SUNLieComplexCoordMatrixLM` to a complex-linear equivalence between
   `SUNLieComplexCoord Nc` and the subtype of traceless complex matrices.
   Do not postulate surjectivity or use a dimension count.  For a traceless
   matrix `Z`, construct the inverse explicitly from
   `A = (Z - Z†)/2` and `B = (Z + Z†)/(2i)`, both skew-Hermitian and
   traceless, so that `Z = A + i B`; then use `suLieCoordIso` on `A` and `B`.
   This is the missing typed route by which `SL(N,C)` conjugation acts on the
   source coordinate fibre.

   Implementation gate: prove injectivity and this explicit surjectivity for
   the already complex-linear `cmp99SUNLieComplexCoordMatrixLM`, then package
   it with `LinearEquiv.ofBijective`.  Do not define the inverse first and try
   to prove its complex linearity through the conjugate-transpose expression;
   the bijective packaging avoids that artificial elaboration wall.

   Proof contract, fixed before implementation:

   * codomain: the existing Mathlib carrier
     `LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ`, i.e. the kernel of the complex
     trace map, not a new predicate-equivalent subtype;
   * injectivity: if `A + i B = 0` with `A,B ∈ su(N)`, conjugate transpose
     gives `-A + i B = 0`; adding and subtracting recover `A = B = 0`, and
     `cmp98AmbientToLieCoordCLM_leftInverse` recovers both coordinate parts;
   * surjectivity: for traceless `Z`, take
     `A = (Z-Zᴴ)/2` and `B = (Z+Zᴴ)/(2i)`.  Prove skew-Hermiticity and zero
     trace of both pieces explicitly, transport them by `suLieCoordIso`, and
     use the witness `complexify(Acoord) + i • complexify(Bcoord)`;
   * packaging: `LinearEquiv.ofBijective` only after those two function-level
     proofs.  No finrank equality, arbitrary inverse, or isometry claim may
     replace either argument.

   Implementation status (PRE-VALIDATION, 2026-08-25): the explicit
   injectivity/surjectivity construction and the final
   `LinearEquiv.ofBijective` packaging are written in
   `BalabanCMP99Eq337PhysicalComplexPerturbedBackground.draft.lean`, with
   oracle readouts added to its scratch audit.  The source still has no
   materialized `.olean` and no compiler/oracle verdict; in particular this
   status does not promote the Eq. (3.37) background dictionary or discharge
   any terminal field.

   Coverage correction (2026-08-25): the repository declaration/readout
   gate found six public helper declarations in that module that the first
   audit list omitted.  Checkpoint `b91d42630efb15f32d4b4ecd242a33238926d4de`
   adds those exact readouts; the six-file Eq. (3.37) coordinate boundary now
   reports `57/57`.  The retargeted gate expects 8, 23 and 26 readouts for its
   three audits.  The earlier 20-readout background queue is superseded and
   cannot be used to claim total oracle coverage.

   Notation correction (2026-08-25): static preflight then found that the
   return type of `cmp99SUNLieComplexCoordSlEquiv` used `≃₁` (Unicode
   subscript digit one).  Checkpoint
   `b70735b82216a0ab1cd9a3bd4e195db1426a83fe` replaces it by the actual
   algebraic `LinearEquiv` notation `≃ₗ`; runner checkpoint
   `737b7b01badeba5811b1bb7ae557c6ea45c4a79e` retargets both C6d and Eq337
   gates to that source.  No isometry or norm-one coordinate bridge follows
   from this equivalence.

   The immediate algebraic consumer is also written as the two-file
   PRE-VALIDATION boundary
   `tmp/C6D-EQ337-COMPLEX-UBAR-COORDINATE-EXPONENT-DRAFT-PATHS.txt`.
   It packages the already literal normalized sum of determinant-one
   `nearLog` deviations in `sl(N,C)`, pulls that constructed matrix back
   through the equivalence, and proves that remapping the coordinate returns
   the same exponent exactly.  Thus the future recursive `Q_j` coordinate is
   generated from the Ubar expression and is not caller data.  This boundary
   has no `.olean` or oracle verdict and proves none of the Proposition-4
   estimates.
1. **Analytic next-background chain.**  Construct every coarsened background
   of the explicit `SL(N,C)` configuration `exp(i eta A') U` by the literal
   complex extension of the CMP98/CMP99 `Ubar` operation.  Printed (3.55)
   consumes `overline{U'U}, overline{overline{U'U}}, ...`; these backgrounds
   are not optional indices.  The producer must recurse from the finest
   background and may not accept a free scale-indexed family.

   Source gate (closed 2026-08-25): CMP99 p. 401 attributes the construction
   and its analytic bounds to CMP98 [5], definitions (52), (53), identity
   (97), bounds (102), (103), (160)--(162), and Proposition 4.  The clean
   2629073-byte primary PDF was materialized from authenticated Drive with
   SHA-256 `03409AD81885593D65535550EAFAC08639E66123D4ACF92462847AE2EE4DD7D6`,
   matching the private source packet.  Targeted 300-dpi renders visually
   confirm each named locator on printed pp. 26, 32, 33, 38, 39 and 42.
   Printed p. 39 states that the Proposition-4 constants are independent of
   `k` and gives the homogeneous expansion (136).  This closes the source
   uniformity gate but does not itself bound the literal matrix
   `UbarDeviation`.  The remaining frontier is the finite complex exp/log
   `Ubar` source-to-Lean dictionary; it may not be replaced by an existing
   reconstruction, a free background family, or a premise named after the
   desired deviation estimate.

   The remaining one-scale estimate is now split into a finite, falsifiable
   chain rather than one free `hdev` field:

   1. from the literal amplitude bound on `A'`, prove a near-one radius for
      each oriented link `exp(i eta A') U`; the compact baseline contributes
      its already named local regularity radius and the exponential
      contributes the sealed `norm_exp_smul_sub_one_le_two_mul` term;
   2. identify the three contour holonomies and inverse coarse transport with
      the single concatenated word `cmp98SourceFourContourEdges`; the group
      identity `wilsonLine_reverse_list` supplies the inverse, so no
      complex-adjoint identity is introduced;
   3. convert the link radii along that one exact word into the literal
      `cmp99SourceComplexLocalizedUbarDeviation` radius with
      `norm_orderedOnePlusProduct_sub_one_le`, preserving the source path
      length and avoiding both a periodic-volume factor and an artificial
      four-factor constant;
   4. discharge the Mercator-ball and no-winding gates from that derived
      radius, then form the trace-zero normalized logarithmic exponent; and
   5. pull that exponent back through the explicit `sl(N,C)` coordinate
      equivalence.  The resulting coordinate is the source `Q_j`; it is an
      output of the preceding four steps, never an input family.

   Each radius in this list is scale-local.  Uniformity in `j` remains the
   separate Proposition-4 composition problem; proving one link/path radius
   must not be reported as the uniform analytic recursion.

   A declaration-level reuse audit now fixes the first implementation split.
   `UbarDeviation`, `UbarDeviation_gaugeAct` and the path/basepoint geometry in
   `Ubar.lean` are genuinely group-generic and may be specialized to
   `Matrix.SpecialLinearGroup (Fin Nc) C`.  By contrast,
   `cmp99PhysicalUbarBlockOfDeviationBudget` is essentially `SU(N)`-specific:
   it closes the exponent through skew-adjointness and packages the result in
   `SUN Nc`.  The analytic constructor must not coerce that physical block.

   The replacement is finite.  First give `SL(N,C)` its defining
   `MatrixRealization` through `Matrix.SpecialLinearGroup.toGL`.  Then prove
   directly that `det D = 1`, `norm (D-1) < 1` and the existing no-winding
   budget imply `trace (nearLog (D-1)) = 0`.  This uses
   `det(exp X) = exp(trace X)`, `Complex.exp_eq_one_iff`, and the already
   sealed trace-norm bound; unitarity is neither true nor needed.  A weighted
   real-mass sum of those logarithms therefore exponentiates into `SL(N,C)`.
   Only after this one-block closure may the literal path deviations be
   assembled recursively.

   That algebraic boundary is now written, but not compiler-verified, as:

   ```text
   tmp/BalabanCMP99ComplexUbarSpecialLinear.draft.lean
   tmp/BalabanCMP99ComplexUbarSpecialLinearAudit.draft.lean
   tmp/CMP99-COMPLEX-UBAR-SPECIAL-LINEAR-DRAFT-PATHS.txt
   ```

   Its exact two-file overlay passes the repository textual guard
   (`LEAN_OVERLAY_TEXT_OK files=2`, one PRE-VALIDATION marker per file).  The
   draft exposes thirteen audit readouts and claims no `.olean`, gauge-background
   recursion or source radius producer.  The next module after it is therefore
   not another abstract `Ubar`: it is the positive-bond localized
   `SL(N,C)` block built from the existing group-generic deviation plus an
   analytic small-field/no-winding certificate, followed by the forced
   finite next-background recursion.

   Acquisition correction, 2026-08-24: the authoritative DOI is
   `10.1007/BF01211042`.  The earlier catalog DOI `10.1007/BF01205787` belongs
   to an unrelated article in CMP 98 and is retained only as incident
   provenance.  Springer currently exposes metadata but not the primary PDF
   without subscription access.  It did not weaken the clean-primary
   requirement; that requirement was discharged separately by the matching
   private PDF and targeted renders recorded above.
2. **One-scale analytic average.**  On each background produced by item 1,
   construct the literal normalized block average as a
   complex-linear map.  The normalization remains `M^{-d}` at each scale.
   The conjugation transport may be a complex-linear equivalence, but no
   isometry field is permitted.
3. **Finite analytic recursion.**  Compose those one-scale averages in the
   printed order `Q_{j-1} ... Q_0`.  The recursion stores the actual
   scale-indexed backgrounds and regions; it may not accept a free terminal
   operator called `Qprime`.
4. **Independent starred synthesis.**  CMP99 does not print a separate
   one-scale starred formula here.  It prints the finite kernel of `Q'_j(U)`
   in (3.19), then says that the real adjoint has a similar expansion.  Derive
   the spacing-weighted algebraic transpose of that finite kernel, verify on
   the compact real slice that it is the source Hilbert adjoint, and continue
   its algebraic coefficients complex-linearly without conjugation.  The
   transpose is characterized by the complex-bilinear extension of the real
   invariant pairing, not by Lean's sesquilinear Hermitian inner product.
   Compose those maps in reverse order as their own recursion.  This object
   is not Lean's Hilbert `.adjoint` away from the real slice.
5. **Real-slice agreement.**  Prove that the analytic average restricted to
   coordinatewise complexifications of real fields agrees with the
   complexification of the existing real retained average.  Prove the
   analogous statement for the starred synthesis and the real weighted
   synthesis.  These are theorems about the two internal constructions, not
   constructor fields supplied by a caller.
6. **Gauge covariance.**  Transport `U` and `A'` together and prove that the
   two analytic recursions intertwine the resulting gauge action.  The
   positive-bond identity in the present scratch frontier is only the leaf
   input to this tower theorem.
7. **Printed differences.**  Build the baseline and perturbed analytic
   towers on identical typed carriers, then define `F'_2(A)` as their
   difference and `F'_2*(A)` as the difference of the independently built
   starred syntheses.  Only at this point can (3.59) and its starred partner
   be discharged definitionally.

The acceptance gate is therefore threefold: no complex transport inhabits a
real-isometry type, no Hermitian conjugation or `.adjoint` occurs in the
analytic starred definition, and both real-slice agreements are proved from
the recursions.  Bounds and holomorphy remain later obligations; this contract
alone moves no terminal counter.

The normalization of item 4 is already determined by (3.19) and the weighted
pairing printed immediately below it.  For a `j`-block owner `y = owner_j(x)`,
the real-slice formulas have the schematic form

```text
(Q'_j(U) lambda)(y)
  = sum_{x in B^j(y)} L^{-jd} R(U(Gamma^j_{y,x})) lambda(x),

((Q'_j(U))^star eta)(x)
  = R(U(Gamma^j_{y,x}))^{-1} eta(y).
```

Indeed the coarse pairing contributes `(L^j eta)^d`, which cancels the
`L^{-jd}` row mass against the fine pairing weight `eta^d`.  Therefore the
analytic starred one-scale constructor must have **unit synthesis mass** and
algebraic inverse transport.  Adding another `L^{-jd}`, a block-cardinality
factor, or a conjugate transpose is rejected.  This is a derived dictionary
lemma whose visual premise is (3.19); it is not being attributed as a second
displayed formula in CMP99.

The sealed real-slice blueprint already exists as
`cmp99SourceTransportedBlockWeightedAdjointCLM`: its source comment and
definition are exactly inverse transport with coefficient one, and its
pairing theorem accounts for the `M^d` Radon--Nikodym ratio.  The complex leaf
must complexify this **algebraic formula** and prove restriction to that map;
it must not complexify the theorem that identifies the real map with a scalar
multiple of Lean's Hilbert adjoint.

There is also a sealed **flat** complex recursion blueprint:

- `CMP99SourceActiveRegionChain.flatExplicitComplexQprime`;
- `CMP99SourceActiveRegionChain.flatExplicitComplexWeightedAdjoint`;
- their two `..._commutes_complexification` theorems; and
- `cmp99SourceFlatComplexBlockWeightedAdjointCLM_map_complex_smul`.

These already establish the finite recursion order, unit synthesis mass and
real-slice agreement when every transport is the flat identity.  They do not
depend on `U'U`, do not encode `SL(N,C)` conjugation and therefore are not the
regional/interacting producer.  The next implementation should generalize
their one-scale leaves to algebraic `SL(N,C)` transport and package the
result as genuinely complex-linear; it must not duplicate the flat induction
or count the flat theorem as (3.59).

The first source-localized `SL(N,C)` background step is now also explicit in
PRE-VALIDATION scratch:

```text
tmp/BalabanCMP99ComplexLocalizedUbarBackground.draft.lean
tmp/BalabanCMP99ComplexLocalizedUbarBackgroundAudit.draft.lean
tmp/CMP99-COMPLEX-LOCALIZED-UBAR-DRAFT-PATHS.txt
```

It reuses only the group-generic contour/base-background substrate, fixes the
mass to `M^{-d}`, constructs positive bonds through the determinant-one
complex Ubar closure, and obtains negative orientations from
`gaugeConfigOfPositiveBonds`.  It accepts no coarse background or Ubar value.
Its sole analytic premise is the named uniform deviation estimate on the
literal `UbarDeviation`; producing that estimate from CMP98 Proposition 4,
(134)--(136), and (160)--(162) requires an explicit finite exp/log transport.
The four-file cumulative overlay is textual evidence only until a Colab
compiler/audit gate passes.

Before that constructor, expose the invariant complex-bilinear pairing `B`
and prove the leaf identity

```text
B (R(g) X) Y = B X (R(g^{-1}) Y),       g in SL(N,C).
```

On `SU(N)` and real Lie coordinates this reduces to the existing orthogonal
adjoint identity.  Using a Hermitian pairing here would introduce complex
conjugation, destroy holomorphy in `A'`, and produce precisely the operator
that CMP99 says is not `F'_2*(A)`.

## Existing scratch prefix that may be promoted, never presumed verified

- `BalabanCMP99Eq335PhysicalForwardDerivative.draft.lean`
- `BalabanCMP99Eq335PhysicalRegularityWitness.draft.lean`
- `BalabanCMP99Eq335PhysicalRegularityLaplacianLocality.draft.lean`
- `BalabanCMP99Eq335SourceRegionDictionary.draft.lean`
- `BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion.draft.lean`

Every one remains scratch/PRE-VALIDATION until a fresh Colab focal and audit
passes.  The existing per-depth generated
`BalabanCMP96SourceSeparatedRegionalPrefixEq342Certificate` is not an
acceptable uniform replacement.

## Atomic promotion boundary before step 1

The five visible endpoints above are not an independently compilable overlay.
Their exact scratch import closure is the 40-path source/audit list in
`tmp/C6C8F5B-FULL-SCRATCH-PATHS.txt`.  The current fail-closed promotion
preview reports

```text
STEP8B24_C6C8F5B_PROMOTION_PREVIEW_OK
files=40
new_declarations=2
new_audit_readouts=2
manifest_sha256=7BB90E48BB18EBFE8777F24D5CBEBA71E3B1B980B7E6AAD137207F73E35D1B29
```

on 2026-08-24 in `0.282` seconds.  This is a Windows-light textual/hash check,
not compiler evidence.  A later Colab gate must materialize and hash all forty
paths atomically; compiling only one of the five endpoints against absent or
stale `.olean` files is not evidence.  The stop-on-first-error order is:

1. retained endpoint geometry plus audit;
2. source-region dictionary plus audit;
3. localized retained prefix plus audit;
4. source-region closure plus audit.

No new overlay is to be launched until the currently running uniform
point-source/localized-field B0 gate has emitted and preserved its terminal
verdict.

The fail-closed materializer is prepared but has not been applied:

```text
tmp/promote_step8b24_c6c8f5b.py
SHA256=1A72CC711A1D6F181D079F23D1E3B3CBC2E6624A2DFA85B25ED9F815BA5CF668
C6C8F5B_MATERIALIZATION_PREVIEW_OK files=40
```

Its default mode is read-only; `--apply` refuses every pre-existing target,
writes the pinned LF-normalized bytes, rehashes the result and rolls back its
own partial writes on failure.  It deliberately preserves all forty
PRE-VALIDATION notices.

### Semantic classification of that overlay

The 40-file closure is **support/interface infrastructure, not by itself the
complete source regularity interface in step 1**.  Its final public wrapper removes the intermediate
`hinside : CMP99Eq335RetainedFineReadCarrierInsideRegularCube` premise by
deriving it from the source-region dictionary, and it exposes no Green or
four-action bound.  However it still receives

```text
W : CMP99Eq335PhysicalRegularityWitness ...
D : CMP99Eq335Corollary36SourceRegionDictionary ...
chain : CMP99SourceUbarRadiusChain ...
```

The scalar `chain` is an already sealed no-winding/log-radius regime, and the
retained carrier inclusion is derived internally.  `W` contains the cube-local
gauge, logarithmic representative, exponential identity and both literal
(3.35) bounds.

Visual inspection of CMP99 printed p. 396 fixes the logical status: (3.35) is
the **definition of the regularity class of configurations**.  It says that
for an arbitrary cube of the stated class and a configuration `U`, there
exists a cube-local gauge and representative satisfying the two bounds.  It
does not assert that every arbitrary `U` has such a witness.  Therefore an
unconditional producer of `W` would be false; the faithful source premise is
membership in that regularity class, quantified over every admissible cube,
and `W` should be derived by specializing that premise to the cube selected
for the regional argument.  Consequently:

- a green validation of the forty files must be reported as a geometric and
  interface prefix only;
- it cannot mark the source regularity dictionary complete or move any
  physical counter merely because one consumer accepts `W`;
- the real step-1 endpoint must introduce the source-faithful
  all-admissible-cubes regularity-class predicate and derive the needed `W`
  for the selected cube;
- retaining that named class-membership premise is legitimate source data;
  replacing it by an arbitrary per-region `W`, or claiming `W` for every `U`,
  is not.

Printed p. 408 independently confirms the downstream quantifier order in
Corollary 3.6: `U` satisfies (3.35), `Omega'_0` lies in one admissible cube,
and `O(1) M alpha0 <= alpha1`; only then do Theorems 3.1--3.3 apply.  The
source PDF is `cmp99/1103942769.pdf`, SHA-256
`39F8033B35838C7BDD14F97C7FB1EDB0B35D4190B8B88F31D19D12A72D542861`.

The corrected all-cubes interface is now written in scratch only:

```text
33767C129BF52C29BA7E1C6B771002C58693E617017D5CF039BDF70AE53B1AEC
  tmp/BalabanCMP99Eq335PhysicalRegularityClass.draft.lean
EEFA756993496832AF7CAA4FF322749979C6C133AA9C0CAC8200F1F5001F5BEC
  tmp/BalabanCMP99Eq335PhysicalRegularityClassAudit.draft.lean
```

It separates cube data from class membership and derives the old one-cube
witness only after the cube and Corollary-3.6 scalar gate are supplied.  Its
two-file textual and import-prefix guards pass; it has not been compiled and
must not be promoted before the corrected B0/C6b retry passes.

The public regional consumer that removes the arbitrary per-region witness is
also written in scratch only:

```text
4BFB3D2748581860A7178795EF3CFE01566D895D7F4C21C667E91303613FD7A0
  tmp/BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTower.draft.lean
AEFD4126CF1182F13F2C5D10ADE4D903AD71E63E59C7AABE9924704C491F4896
  tmp/BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTowerAudit.draft.lean
```

Its contract receives class membership, the selected regular cube, the
literal source-region dictionary and the separate Corollary-3.6 scale gate.
It constructs `W` internally and then calls the geometric prefix.  The
four-path boundary and both guards are recorded in
`tmp/C6D-EQ335-REGULARITY-CLASS-CONSUMER-PATHS.txt`.  This is still static
work: it has no compiler verdict and does not move a counter.

The four-file promotion boundary is now fail-closed and reproducible:

```text
C6D_EQ335_PROMOTION_PREVIEW_OK files=4 declarations=5 audit_readouts=5
  manifest_sha256=541381D7C8238DF851A372C0A84489FA96F5709418A8146BAF60811B15EA21AE
1B5E133889C8CB42DB98F83586B6B8A5B601D87D9176D474E2E43F07FC217C67
  tmp/audit_c6d_eq335_regularity_class_promotion_preview.py
9847568F74F0AE6308F2E0219E3F5C0F2D1B79198631B1FC8C47DCFD84F565F2
  tmp/promote_c6d_eq335_regularity_class.py
```

The materializer remains read-only by default.  Its `--apply` mode refuses
to run until the exact regularity-witness and source-region consumer targets
from the forty-file prefix exist; it then refuses every collision, preserves
all four PRE-VALIDATION notices and rolls back its own partial writes on
failure.  It has not been applied.

### Public-input audit of the forty-file prefix

A declaration-by-declaration static scan confirms that `fineSmall` is confined
to the low-level localized-`Ubar` constructors, and `hinside` is confined to
the intermediate regularity-witness methods.  Neither survives the
source-region wrapper, and neither survives the new regularity-class wrapper.
No value, derivative, Laplacian or Green bound is an input to either final
endpoint.  The surviving public data are exactly:

- source membership `R : CMP99Eq335PhysicalRegularityClass ...`;
- the selected regular cube `C` and literal source-region dictionary `D`;
- the explicit Corollary-3.6 scale inequality `hscale`;
- the generated region chain and its scalar construction regime
  (`hM`, `rho`, `halpha1`, `chain`).

`CMP99SourceUbarRadiusChain` is already a purely scalar inductive regime: its
constructors store nonnegativity, no-winding and logarithmic-radius
inequalities, but no background field or linkwise estimate.  Thus the prefix
does not rename a missing physical Green estimate as a hypothesis.  This scan
is static evidence only and does not replace the pending Colab build.

### Closed promoted boundary between (3.35) and (3.36)

The ordinary physical chain described below is no longer a scratch candidate.
It was promoted at source checkpoint
`f85f09480ffda5502cbd60884eac387ab646a8b5` and sealed from a fresh Colab
Pro+ checkout by runner checkpoint
`2ef06bdf8667f489aeb2de0a7921cff0d866bc19` (runner Git-blob SHA-256
`B313217094E663DAAE9BB8F548422676683E614181DE9021BE6690698144C021`).
The cold root completed 10,907 jobs in `8120.232` seconds; all five direct
audits passed, covering 37 declarations. Canonical evidence SHA-256 is
`0A2D7A57CC681CEDCBB47D6FEC8FFC0CC2114A0B392AEB2A6980AA2207C31851`;
the independently rehashed archive SHA-256 is
`FCC92924A3E3DAEDC0363FF94B9FFAC8BCAF15742A3AF78545862917A44E46D8`.

The promoted endpoint is the named theorem
`cmp99PhysicalDStarOneCochain_inner`. Its proof avoids the spurious factor two
by splitting ordered direction pairs exactly once and transporting the
concrete plaquette sum through `cmp99PhysicalPlaquetteSigmaEquiv`. The ten
module-level PRE-VALIDATION notices can therefore be retired by the seal
commit. The historical pre-seal design record below is retained to make the
factor-two gate and its resolution auditable; every claim there that the
ordinary Eq. (3.35)/(3.36) chain is only scratch or unelaborated is superseded
by this paragraph.

This closure remains deliberately below the regional analytic endpoint: it
constructs no Green family, regional `B0` or `delta0`, does not attain window
15, and does not move a terminal counter. Counters remain `20/41`,
`TermSource = 0`.

#### Historical pre-seal design record

Printed p. 396 states that the operators used up to Theorems 3.1--3.3 need
only (3.35); the later `G/H` layer additionally needs (3.36).  A repository
scan finds no current realization of the literal second condition
`|d_eta^* d_eta A| < O(1) M alpha0 (L^j eta)^-3`.  In particular:

- `BalabanCMP99Eq335PhysicalCovariantDerivative.draft.lean` is already
  retracted and represents the later covariant tensor `D^U A`, not (3.35) or
  (3.36);
- `cmp99PhysicalForwardOneDerivative` is the correct full ordinary
  first-difference tensor for (3.35), but iterating it generically would not
  identify the exterior/codifferential composition printed in (3.36);
- `FiniteTorusCurlDiv.lean` supplies the forward difference, ordered curl,
  backward difference and summation-by-parts substrate, but no named physical
  `d_eta^* d_eta` one-cochain operator yet.

Therefore the present C6d `G'` bridge must consume only class membership for
(3.35).  The later `G/H` bridge needs a separately source-checked (3.36)
operator and class extension; it must not strengthen this interface now or
rename (3.36) as an arbitrary second-derivative bound.

A two-file scratch candidate now makes that later boundary concrete:

```text
7628A08230E67C808C2FEA916D96F64F7D3E8152003F5ECF47DB69690F9B1909
  tmp/BalabanCMP99Eq336PhysicalDStarDRegularityClass.draft.lean
7AD3CB30A13016754EAEAA4FCBB08843D4CC48A58AD7DFCA47FDF5158005A781
  tmp/BalabanCMP99Eq336PhysicalDStarDRegularityClassAudit.draft.lean
40883BFCD9F13E4D8FD1DCFA9C3FCA405D89FBB821C66EC75E33B00592890131
  tmp/CMP99DStarPairSummationByPartsRepro.lean
95930820F739BC294A2B3D9D85C15A6092B95F1DF15730D1F8CD56DA6456E448
  tmp/C6D-EQ336-ADJOINT-PATHS.txt
```

It keeps both `eta^-1` factors visible, stores the (3.35) cube datum inside
the stronger (3.36) datum, and derives the weaker all-cubes class by
forgetting the `d_eta^* d_eta` bound.  Text and import-prefix guards pass.
It is deliberately not in either promotion boundary: before promotion its
negative-backward-difference convention must be tied to the source by a named
one-/two-cochain adjointness theorem, then compiled and audited.  No present
counter or C6d `G'` endpoint depends on it.

The static sign/orientation audit now fixes the exact convention that theorem
must express.  `PhysicalGaugeTwoCochain` is indexed only by concrete
plaquettes `mu < nu`, while `torusCurl` is defined for every ordered pair and
is antisymmetric.  For an ordered-plaquette field `F`, extend it by

```text
F_ord(mu,nu) = F(mu,nu)       when mu < nu,
              -F(nu,mu)      when nu < mu,
               0             when mu = nu.
```

Then finite-torus summation by parts gives, with no factor two,

```text
(d_eta^* F)_nu = -eta^-1 * sum_mu backward_mu F_ord(mu,nu).
```

Indeed the `mu < nu` plaquettes contribute the negative-backward term, while
the `nu < mu` plaquettes contribute the positive term through the
antisymmetric extension.  Taking
`F_ord(mu,nu) = eta^-1 * torusCurl A mu nu` is therefore exactly the scratch
candidate `cmp99PhysicalDStarDOneCochain`.  The missing compiled gate is now
sharply named: define the antisymmetric extension and the scaled full
one-to-two differential, then prove that this explicit codifferential equals
its Hilbert adjoint (equivalently, prove the global inner-product identity).
Using a sum over all ordered direction pairs without the `mu < nu`
normalization would introduce a spurious factor two and is rejected.
The three-file exact path manifest passes the repository's lightweight overlay
gate (`LEAN_OVERLAY_TEXT_OK files=3`): no `sorry`/`admit`, balanced command
scope and balanced delimiters.  This remains textual evidence only; all new
declarations and the pairwise summation-by-parts proof are still awaiting a
Colab elaboration and axiom audit.  The pairwise proof is duplicated in the
minimal `FiniteTorusCurlDiv`-only repro so that its first elaboration does not
pay for the full CMP99 physical import graph.

The scratch boundary now also contains `cmp99SumOrderedPairSplit` (and the
minimal `_repro` copy).  It proves the finite triangular reindexing directly:
the diagonal is zero and the two ordered orientations are combined exactly
once under `mu < nu`.  This is intentionally not phrased through `Sym2`, since
the lower/upper orientation determines which one-cochain component and which
backward derivative occur.  Together with the pairwise summation-by-parts
theorem it removes the combinatorial source of a factor two.  It does not yet
prove the global `PiLp` adjointness identity: that final composition still has
to expand the one-cochain inner product, apply the ordered-pair split, and
identify the concrete-plaquette sum.  No adjointness record or equality is
assumed in its place.

The concrete-plaquette side is now likewise explicit rather than dependent on
the repository's internal `Fintype` enumerator.  The scratch equivalence
`cmp99PhysicalPlaquetteSigmaEquiv` identifies a physical plaquette with
`Sigma x, Sigma mu, {nu // mu < nu}`, and
`cmp99SumPhysicalPlaquette_eq_sigma` transports arbitrary additive sums along
that equivalence.  Both have minimal-repro copies.  The remaining global gate
is therefore algebraic and finite: expand the one-cochain `PiLp` inner product,
apply the ordered-pair split plus the pairwise summation-by-parts identity, and
finish through this explicit plaquette-sum equivalence.  These new declarations
remain unelaborated PRE-VALIDATION source; the exact-path text guard alone does
not certify them.

The final theorem is now fixed at statement level, with no adjointness datum as
an input:

```text
inner R A (cmp99PhysicalDStarOneCochain eta F)
  = inner R (cmp99PhysicalScaledD1OneCochain eta A) F.
```

Its finite normal form is likewise fixed.  Expand the left `PiLp` inner
product as `sum_x sum_nu`, move the site sum inside, and call the summand

```text
T(mu,nu) = sum_x inner A(x,nu)
  ((-eta^-1) * backward_mu (F_ord(mu,nu)) x).
```

`cmp99SumOrderedPairSplit T (fun mu nu => T nu mu)` changes the unrestricted
ordered sum into one term for each `mu < nu`.  On that branch the two terms
are definitionally the negative-backward and positive-backward summands of
`cmp99PhysicalDStar_pair_inner`; its conclusion is exactly the scaled curl
paired with the independent plaquette value.  A single elementary helper

```text
sum_nu (if h : mu < nu then f nu h else 0)
  = sum_{nu : {nu // mu < nu}} f nu.1 nu.2
```

then converts the triangular `if` sum to the proof-carrying subtype.  Commuting
the remaining finite site sum and applying
`cmp99SumPhysicalPlaquette_eq_sigma` produces the right `PiLp` inner product.
This pipeline consumes only already named finite identities; it introduces no
regularity, source dictionary or operator equality as a hypothesis.  The
subtype helper, the global theorem and their audit readouts must first pass in
the minimal repro and then in the physical module before any promotion.

## Acceptance invariants

- no free Green family, perturbation norm, relative inverse estimate or
  regional `B0/delta0`;
- no identification of generated and source coefficients;
- no global extension of a cube-local source theorem;
- no loss of the source-owner orientation;
- no source-cardinality factor;
- no generated CT+Schur route declared as physical attainment;
- counters stay `20/41`, `TermSource = 0` until an actual terminal producer is
  installed.

### Post-Eq337 analytic Ubar boundary (STATIC; promotion gated)

The next analytic background boundary is now frozen as exactly three
source/audit pairs in `tmp/C6D-COMPLEX-UBAR-DRAFT-PATHS.txt`.  The lightweight
guards report six PRE-VALIDATION files and complete `25/25` public-declaration
axiom coverage, including the named `MatrixRealization` instance for
`SL(N,C)`.  Its promoted-byte manifest is
`EAF815BF6D97C069A1887F755A4DF606B2B890BE910E2533AB716049097CF603`.

The boundary constructs internally:

1. tracelessness of the principal Mercator logarithm from determinant one and
   the explicit no-winding budget;
2. the determinant-one weighted Ubar factor in `SL(N,C)`;
3. its exact physical complex coordinate through the Eq. (3.37)
   `sl(N,C)` equivalence; and
4. one literal oriented next-background step from the fine background.

It does **not** construct the path-product deviation estimate.  The surviving
premise

```text
forall b x, x in blockOf M N' b.1 ->
  norm (literalUbarDeviation background b x - 1) <= budget.delta
```

is therefore a named analytic obligation, not a produced theorem and not a
free next background.  The forced finite recursion and the producer of this
uniform deviation bound remain downstream work.  Materializer
`tmp/promote_c6d_complex_ubar.py` refuses `--apply` while the exact Eq. (3.37)
complex perturbed-background source/audit pair still carries PRE-VALIDATION.
Thus this static boundary cannot be stacked on an unsealed coordinate gate.
It moves neither `20/41` nor window 15 and does not instantiate `TermSource`.

#### Exact producer still required for `hdev`

Static inspection rules out reusing the sealed special-unitary linear path
estimate unchanged.  The Eq. (3.37) fine background takes values in
`SL(N,C)`, so its links are determinant one but are not unitary off the real
slice.  In particular, `norm_wilsonLine_sub_one_le_length_mul` obtains its
linear path-length constant from unitary contractivity and is not a producer
for the complex path product.

The missing producer therefore has three explicit stages:

1. derive one oriented-link radius for
   `cmp99Eq337PhysicalComplexPerturbedBackground` from the physical link
   radius and the printed exponential perturbation, including the negative
   orientation rather than importing unitary inversion;
2. rewrite each literal Wilson line as the ordered product of its matrix
   deviations and apply the already sealed generic
   `norm_orderedOnePlusProduct_sub_one_le`, retaining its visible
   `length * r * (1+r)^length` cost; and
3. combine the three contour products and the straight base product in the
   literal four-factor `UbarDeviation`, then discharge the single comparison
   with `B.delta`.

This leaves a source-smallness inequality on the physical background and the
Eq. (3.37) complex coordinate norm as the genuine analytic inputs.  It does
not accept the finished `hdev`, a preselected complex background or a free
path-product bound.  The producer must cite the exact contour length lemmas
and the same source read carrier as the sealed real-slice deviation theorem;
no global fine-link smallness or unitarity outside the real slice may be
introduced.

Static inspection fixes the shape of the first-stage constant but also
exposes one additional norm bridge.  The corrected type of
`cmp99SUNLieComplexCoordSlEquiv Nc` is an algebraic `LinearEquiv` (`≃ₗ`), not
an isometric equivalence.  The earlier scratch spelling used the Unicode
subscript digit one (`≃₁`); treating that typo as an isometry would be both a
parser error and a false analytic conclusion.  The producer must therefore
construct a named bound

```text
norm (cmp99SUNLieComplexCoordMatrixLM Nc Z) <= Ccoord * norm Z
```

from the explicit real/imaginary matrix realization.  It may use a proved
continuous-linear operator norm or a sharper explicit coordinate estimate,
but it may not silently set `Ccoord = 1`.  With

```text
q = |eta| * Ccoord * rA,
rLink = epsilonU + 2*q,
q <= 1/2,
```

`norm_exp_smul_sub_one_le_two_mul` gives the exponential contribution.  On a
positive bond the literal factorization is `exp(eta*A) * U`; on the reversed
bond its inverse must be rewritten as `U^-1 * exp(-eta*A)`.  The physical
`U` factor and its inverse have norm one, so both orientations have the same
visible `rLink`.  This is a source-specific theorem about the literal
Eq. (3.37) background, not an abstract inverse estimate on `SL(N,C)`.

After that oriented-link theorem, each path is definitionally an ordered
product of `1 + (link - 1)`, and
`norm_orderedOnePlusProduct_sub_one_le` supplies exactly

```text
path.length * rLink * (1 + rLink)^path.length.
```

The six-file scratch layer now fixes that bridge concretely by defining
`cmp99SUNLieComplexCoordMatrixCLM`, taking the visible chart budget to be its
operator norm, and proving
`norm_cmp99SUNLieComplexCoordMatrixLM_le` by `le_opNorm`.  This is a finite-
dimensional existence bound, not an isometry or an optimized coordinate
constant; it remains PRE-VALIDATION with the rest of the layer.

The positive-orientation consumer is likewise written, but still scratch,
as the two-file boundary
`tmp/C6D-COMPLEX-UBAR-LINK-RADIUS-DRAFT-PATHS.txt`.  It derives the literal
radius

```text
epsilonU + 2 * (|eta| * Ccoord * rA)
```

for `exp(eta A) U` using the named chart budget and the physical `SU(N)` link
norm one.  The path-product estimate remains downstream before this leaf can
feed `hdev`.

The same scratch source proves the analytic negative-orientation model
`U dagger * exp(-eta A)` with exactly the same radius and now closes the
previous algebraic gate separately: coercing the inverse positive `SL(N,C)`
bond is proved equal to that ordered product by a literal left-inverse
calculation (`exp(-X) exp(X) = 1` and `U dagger * U = 1`).  A second theorem
identifies the public negative edge of the reconstructed background with the
same model.  No abstract inverse-norm estimate replaces the source
orientation.

The exact scratch hashes are:

```text
AAE17F83297F96C27FE1A44800166C53FA8BD390F2265E7F4D88F67AF9048984
  tmp/BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadius.draft.lean
004DEC0C3BA76A6E98E57203BA0B1758761193C40E2ABC907E5BEED30249E4D7
  tmp/BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadiusAudit.draft.lean
0A0A80FEA592B580142360B515E7CDB63410A0AE1CA91AE5B36E5C4761441185
  tmp/C6D-COMPLEX-UBAR-LINK-RADIUS-DRAFT-PATHS.txt
```

The lightweight gates pass at `2/2` files and `5/5` declaration/readout
coverage.  This is textual/static evidence only; the pair is not promoted,
compiled or oracle-checked.

The physical `SU(N)` endpoint
`norm_UbarDeviationLogArg_le_four_factors` is **not** a valid consumer for
the complex continuation: its four bare summands use operator norm one of
unitary factors.  The literal `SL(N,C)` paths are not unitary.  The replacement
is the PRE-VALIDATION pair

```text
tmp/BalabanCMP99ComplexFourFactorDeviation.draft.lean
tmp/BalabanCMP99ComplexFourFactorDeviationAudit.draft.lean
```

which specializes `norm_fourMatrixProduct_sub_le_heterogeneous` against four
identity matrices and retains the three preceding complex factor norms in
every telescoping summand.  The named contour lengths must therefore feed
both path deviations and path norm budgets (eventually the visible
`length * r * (1+r)^length` and `(1+r)^length` bounds).  The fourth factor
still requires the exact inverse-coarse-path bridge.  Only after those gates
does the resulting heterogeneous scalar budget face `B.delta`; neither the
unitary four-summand lemma, a free path-product estimate nor a global
fine-link hypothesis is an accepted substitute.

Static-only hashes for this PRE-VALIDATION pair are:

```text
039B6D203ABCB3F834CE7C24B2A8E0F5B8E1F9154A1926371EE6E47C0ED4286F
  tmp/BalabanCMP99ComplexFourFactorDeviation.draft.lean
92839A61D39512E60EDFCF79925F80AADDC950BE4EC7056B5E067E532092E751
  tmp/BalabanCMP99ComplexFourFactorDeviationAudit.draft.lean
95516C3FCCE3BF942B6A32EEDE80F74B47160389DEDB63A5B39C70BFF4FDFC9B
  tmp/C6D-COMPLEX-FOUR-FACTOR-DEVIATION-DRAFT-PATHS.txt
```

The overlay-text and import-prefix gates pass for `2/2` files and the audit
surface is `2/2`.  This is not compiler or oracle evidence.

The next PRE-VALIDATION pair closes the path-level *shape* without importing
the unitary path lemma:

```text
tmp/BalabanCMP99Eq337PhysicalComplexWilsonLineRadius.draft.lean
tmp/BalabanCMP99Eq337PhysicalComplexWilsonLineRadiusAudit.draft.lean
```

It identifies a coerced `SL(N,C)` Wilson line with the ordered product of its
literal link deviations, combines the positive and negative Eq. (3.37) link
theorems into one oriented-edge radius, and derives both

```text
norm(path - 1) <= length * rLink * (1 + rLink)^length
norm(path)     <=                  (1 + rLink)^length.
```

The second line is portante: it supplies exactly the factor norms retained by
the heterogeneous four-factor consumer.  The pair now also packages four
literal complex Wilson paths into the heterogeneous four-factor budget; this
still does not identify those paths with the source Ubar contours.  The
scratch hashes are:

```text
DC8B4021877AF05D78C116CB4319AEF08B5A183CDC1EDDC6777CEDCA811D2990
  tmp/BalabanCMP99Eq337PhysicalComplexWilsonLineRadius.draft.lean
621E804FC0F10E62E0AC7140609BAA268B3169A8668C2DB94EA4D97468C7286A
  tmp/BalabanCMP99Eq337PhysicalComplexWilsonLineRadiusAudit.draft.lean
F590776708CBC62F36EFBC501A871DAE3F88C5BC4BAC53D7EFD06FFD448E8EB2
  tmp/C6D-COMPLEX-WILSON-LINE-RADIUS-DRAFT-PATHS.txt
```

The lightweight gates pass for `2/2` files with `8/8` declaration/readout
coverage.  These theorems are still uncompiled scratch and do not yet install
the four source contours into the complex Ubar `hdev` field.

The source-specific PRE-VALIDATION pair is now written:

```text
tmp/BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius.draft.lean
tmp/BalabanCMP99Eq337PhysicalComplexUbarDeviationRadiusAudit.draft.lean
```

It fixes the first three factors to `Gamma1`, `Gamma2`, and `Gamma3`, and the
fourth to the reversed straight representative of the positive coarse bond.
The exact equality uses `OrientedLatticePath.holonomy_symm`; it does not
estimate an inverse or accept a free coarse field.  It then specializes the
complex four-path budget to the literal Eq. (3.37) background.  A separate
lemma proves that all four paths, including the reversed fourth path, obey the
same `d * (M - 1)` source envelope.  Static-only hashes are:

```text
C0174643F71AFD11FFAFB281B0FFC4C6F171A19DA8410CC5D768490C8AF0B6C6
  tmp/BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius.draft.lean
2C14AE02293417F4060710808B6289355B2D4B677184094A6153C05543083601
  tmp/BalabanCMP99Eq337PhysicalComplexUbarDeviationRadiusAudit.draft.lean
2A881FA25EC08F733B0E17E1CE04317FCD24736F2BBF6969D1A8FD4D4C559088
  tmp/C6D-COMPLEX-UBAR-DEVIATION-RADIUS-DRAFT-PATHS.txt
```

The exact overlay-text gate passes for `2/2` files and the audit surface is
`5/5`.  This remains static evidence only: no `.olean` or axiom-oracle verdict
exists, and no terminal field or scalar window is discharged.
