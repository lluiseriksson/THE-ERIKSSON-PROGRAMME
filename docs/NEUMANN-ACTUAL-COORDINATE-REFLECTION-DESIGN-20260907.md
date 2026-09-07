# Actual full-Green coordinate reflection: finite design gate

STATIC DERIVATION ONLY, not compiler evidence. Source context327a79d3e;
the common-block translation diagnostic is running separately. No new Lean
source is shipped by this note, and no counter or production label changes.

## Why the existing reflection theorem is not the endpoint

BalabanCMP89Eq246FullEndpointReflection fixes depth1, negates every momentum
coordinate and exchanges the two endpoints through the transposed solver.
It is not the required arbitrary-depth, one-coordinate, common half-cell
reflection of the literal non-transpose Green. Keep that theorem unchanged.

The inspected actual precision is diag(fine)+a*column*row, with column
u(q), row u(-q), and u_N(q) the normalized finite negative-exponential
average. The checked diagnostic1182 states u_N(-q)=D(q)*u_N(q),
where D(q)=exp(i*q*(N-1)/N), including the central mode and N=1.
For a coordinate reflection, D uses that coordinate only, not a product
over coordinates that were not reflected.

## Fix the physical scale before the permutation

Set N=L^j>0. The alias carrier is definitionally the centered vectors for
N; use the existing centered-vector Pi equivalence and the scalar residue
reflection on one coordinate. Do not use literal negation on the half-open
even carrier. The reflected alias represents -m modulo N in that coordinate
and m elsewhere. Its associated fine momentum is -q modulo2*pi*N there.
Every factor consuming this congruence needs its own period theorem.

## Six finite outputs to construct, in order

R1. A one-coordinate alias permutation, with unchanged-coordinate and
reflected-residue equations, involution and preservation of the central
alias. At arbitrary j, pin carrier and fibre explicitly; do not identify
the depth-one API with it by unproved definitional reduction.

R2. Literal symbol identities under simultaneous coordinate momentum and
alias reflection: fine'=fine, column'=D*column, row'=D^-1*row.
The half-cell finite-average phase supplies the reflected factor; the
other product factors are unchanged. Period2*pi*N handles wrapped aliases.
D is a concrete exponential and never zero. This gives entrywise
A'[P m,P n]=D_m*A[m,n]*D_n^-1, not an assumed Green covariance.

R3. Transport the solution of the literal alias equation through that
diagonal phase and permutation. Use the already constructed full-solver
domain at both momenta and the literal full-solution equation. Establish
uniqueness from its square finite matrix, not a supplied inverse identity.
The required theorem ALREADY EXISTS:
cmp89Eq246EntireAliasPrecisionMatrix_mulVec_injective, in
BalabanCMP89Eq246AliasPrecisionUniqueness. It takes exactly fine,
stabilized and row nonvanishing; surjectivity is constructed from the
literal solver and finite dimensionality gives injectivity. Its selective
cold seal is1bda3dd70, ledger1056. Do not duplicate this theorem or add a
new uniqueness hypothesis. FinePointSourceSolutionCycle demonstrates its
existing use after transporting an actual source equation; reflection
needs the additional diagonal phases, not a new uniqueness principle.

R4. Reflect both fine integer endpoints about the block centre:
S_N(x)_mu=N-1-x_mu in the selected coordinate, unchanged elsewhere.
After reindexing aliases and negating that momentum coordinate, the target
phase is target*D^-1 and the source phase is D*source. R3 cancels them
termwise. This is a two-endpoint identity for the non-transpose integrand,
not the displacement-only (2.48) kernel and not endpoint exchange.

R5. Integrate the signed momentum change over the symmetric Brillouin cube
with the literal normalization. Supply the actual change-of-variables
lemma and its measure/integrability requirements, rather than assuming
the integral invariant. The complete solver domains must come from the
same common-polistrip hypotheses on both signed slices.

R6. The required lower half-cell reflection is S_0(x)=-x-1 in that
coordinate. It equals S_N(x)-N. Apply the common BLOCK translation theorem
to BOTH reflected endpoints with integer shift -1 in that coordinate.
This is exactly where the pending five-lemma translation consumer enters.
Upper half-cell reflection then differs by an integer block translation
when the physical side is N times its block count. Cite that dictionary.

## Acceptance boundaries

The phase accounting above is a checked-on-paper algebraic design, not a
Lean theorem. It must survive R1-R6 without replacing the actual operator.
N=1, central aliases and full-period carrier sides are not removed.
Neither source-image summability nor a permutation of source images proves
the target Neumann seam. That seam and the image-series precision equation
remain M4 in NEUMANN-MIXED-BOUNDARY-CANDIDATE-20260907.md. The normalized
fine-density-to-counting factor N^-4 must still be installed exactly once.

20/41; TermSource=0; window15 compatible, not attained.

## Bounded R1 scratch preparation while translation compiles

tmp/NeumannCoordinateAliasReflectionDraft.lean constructs the one-coordinate
permutation from already sealed scalar-reflection and product-equivalence
modules; it does not import the pending translation draft. Six audit targets
cover the two product-coordinate equations, unchanged integer coordinates,
selected-coordinate residue negation, involution and finite-sum reindexing.
Explicit central-alias preservation and specialization N=L^j remain to add.
Nothing from this draft is in the running queue. Text guard only: exit0,
0.0855034s,15273984bytes observed peak RSS; compiler status NOT CHECKED.
Two local invocation mistakes (missing manifest argument, then str instead
of Path in the direct checker call) were corrected without any Colab run.

The subsequent scratch revision adds the explicit physical permutation on
CMP89Eq246AliasIndex d L j and its central-alias preservation theorem.
The NeZero(L^j) instance is constructed from NeZero L; j=0 and N=1 are
retained. Seven audit declarations are now present, all NOT CHECKED.
Both text and import-prefix guards pass; this is not compiler evidence.

## Prepared retained-runtime diagnostic, deliberately locked

tmp/colab_neumann_coordinate_alias_reflection_hot.template.py and the
matching verify_neumann_coordinate_alias_reflection_hot.template.py target
source6804b00aadf10ea9181044d150128c8942b9e7c7, draft blob SHA256
ffb4bbab01f8f49b593d2f2657f12a499232501a54bb64638c0320c8d28aea3e.
The runtime checkout must remain327a79d3e; only the named scratch overlay
is added after the ongoing common-translation diagnostic is preserved.
Parent archive/report/olean pins and the final runner hash are deliberately
unset. Tests confirm the runner refuses BEFORE network or filesystem writes
(exit0 test,0.1247246s,16470016bytes observed RSS) and the reader refuses
before opening evidence (exit0 test,0.1040106s,14528512bytes observed RSS).
These are templates, not launched scripts and not Lean evidence. After
actual parent PASS and preservation, fill actual pins, test the final reader
against synthetic corruptions, publish by fast-forward, then run once in the
same warm runtime. If the current diagnostic fails, repair it first instead.

## Actual R1 HOT launch after independent parent preservation

Parent diagnostic is VERIFIED_DIAGNOSTIC_PASS, ledger1186, preservation
892151b866cf474d6dc14ad74f20feaf3f93e35e. Final runner
4de83287ad5a0ea7515946fe3b376440a5a354a4, Git-blob SHA256
55ccd9d7db084238a5b164eb1d53efcd65f03f32078b437b3325d79a3a7218cb.
Independent reader/tests published b41de5843: one synthetic valid case,
13 corruptions rejected, exit0/0.2690323s/23142400bytes observed RSS.
These are instrument tests, not Lean evidence.

One HOT launch2026-09-07T01:32:50.664065UTC, PID22599, same retained
runtime930e719ad438, tab22. Hash gate PASS; no previous Lean/Lake process
or R1 output existed at preflight. Source6804b00aadf10ea9181044d150128c8942b9e7c7.
Log /content/launch-coordinate-alias-reflection-hot-v1.log.
Archive /content/neumann-coordinate-alias-reflection-hot-v1-evidence.tar.gz.
Do not relaunch; preserve terminal result with the independent R1 reader.
20/41;TermSource0;no production seal or reflection covariance yet.

FINAL: R1 HOT independently VERIFIED_HOT_PASS, ledger1187. Seven names,
eight stages exit0; draft6.687299610s after71.839149155s warm prerequisites.
Archive5dc24e2d6dde65fffee13758930a6af361c521018a9695f38230ab8f3e1737b5;
reportf9ff4882e748ee7e5233f06e206ac07ad43cad10bd8590a2c9b4ba7bc9bc30a4.
Source unchanged6804b00aa; R1 diagnostic completed, R2-R6 remain open.
Next prepare the actual coordinate symbol transport, consuming the finite
average half-cell phase and explicit wrapped momentum period. Do not replace
it by the depth-one transpose reflection. Production promotion still pending.

Prepared R2a scratch NeumannCoordinateMomentumCarryDraft.lean has four
NOT-CHECKED declarations: momentum-coordinate involution; actual physical
wrapped alias momentum with integer carry supported only on the chosen
coordinate; fine-symbol coordinate symmetry; physical fine-alias symmetry.
The carry is derived from R1 residue negation, not given as a hypothesis.
The existing period theorem uses ((L^j : Nat) : Real), while the physical
fine symbol uses (L : Real)^j: the final transport explicitly uses Nat.cast_pow.
This is a convention equality, not a change of spacing or operator. The
averaging column/row phase is R2b and remains to write before full R2 closes.

R2b is now drafted (not checked) in NeumannCoordinateAveragePhaseDraft.lean:
explicit nonzero exponential D, D(-z)=D(z)^-1, the actual coordinate product
phase, column D, row D^-1, and literal matrix-entry conjugacy. No averaging
factor is assumed nonzero. The diagonal case uses only D≠0; the off-diagonal
case uses injectivity of the constructed R1 permutation. Thus the full matrix
identity is a derived conclusion, not an input or a transpose replacement.

Next queue is finite and stop-on-first-error:
1. Mathlib-only NeumannCoordinateProductRepro (one-factor product identity),
   before project prerequisites; one audited declaration.
2. Existing NeumannHalfCellPhaseRepro (one declaration).
3. Project prerequisites for R1 and EntireAverageAmplitude.
4. Existing NeumannEntireAverageHalfCellPhaseDraft (one declaration).
5. R1 NeumannCoordinateAliasReflectionDraft (seven declarations).
6. R2a NeumannCoordinateMomentumCarryDraft (four declarations).
7. R2b NeumannCoordinateAveragePhaseDraft (six declarations).
All six inputs must be Git-blob pinned, scratch oleans installed in order,
20 exact axiom names total. The fresh run remains a diagnostic until the
production promotion contract is explicitly prepared. No CI exploration,
local Lean or live Colab session has been started for this new queue.

Pinned diagnostic prepared: source95c757465455c7e8cffcfcd6d9d18aa56f6d5083,
runner1f5443d50fbfb21d02a4f817137a3798de05ab0a, Git-blob SHA256
18fd5b9087dd32add221ef56cf49604cc21e730f027c322a2ee95242f0fdb28c.
Independent reader accepts one synthetic fixture and rejects17 corruptions;
producer/reader queue AST agrees exactly. Instrument test exit0/0.3691525s,
21086208bytes observed peak RSS. No compiler conclusion follows from tests.
Six scratch sources/outputs,20 exact audit names, two repros before the
project prerequisite build; retained-runtime policy allows bounded repairs.

Actual launch2026-09-07T01:47:24.455250UTC, PID8249, tab23,
cellHhlGa5HMi3Ja. CPU/high-RAM selected before connection; account
lluiseriksson@gmail.com. Published notebook07d068c15ad86ac8c7c570dac35206ff7c75f59f
visually checked, GitHub notebook confirmation accepted once, HASH_GATE=PASS
with exact SOURCE95c757465 and runner revision. No compiler result yet.
No cell replacement or second launch. Preserve tab with per-turn handoff.

## R3 finite-system transport: static endpoint fixed while R2 runs

Re-read AliasPrecisionUniqueness and FinePointSourceSolutionCycle directly.
Use the former's existing three nonvanishing gates, not a new inverse input.
For the constructed permutation P and actual phase D, define internally
Tf(k)=D(P^-1 k)*f(P^-1 k). R2 says A'(Pm,Pn)=D(m)*A(m,n)/D(n).
The finite-sum change n=P(l) then gives A'*(Tf)=T*(A*f), with each D(l)
cancelling its inverse; this costs no norm estimate and assumes only the
already constructed exponential nonvanishing, not nonvanishing of averages.

The next solution theorem should first quantify over an arbitrary SOURCE
vector, not over an already chosen family of solutions. Both solutions are
cmp89Eq246StabilizedAliasFullSolution, constructed internally. The base
literal solver equation yields A'*(Tsolution)=Tsource; the reflected literal
solver equation yields A'*solution'=Tsource. Existing injectivity at the
reflected momentum identifies them. Exactly base/reflected
CMP89Eq246FullSolutionDomain are visible inputs, as in the sealed cycle
theorem. Their later physical production must use the common polistrip;
no Green covariance, inverse family or extra uniqueness field is accepted.

R4 then proves separately that the reflected physical point-source vector
is Tsource, using both endpoint reflection and the wrapped integer phase.
This avoids making the point-source phase a hidden premise of R3. The
matrix-action transport is a Mathlib-only repro candidate before any new
project bootstrap. No new R3 Lean module is stacked on the running R2 queue.

Independent repro now prepared as tmp/NeumannDiagonalTransportRepro.lean,
NOT CHECKED and not part of the running R2 queue. It states action at Pm,
functional action, and uniqueness transport for finite field-valued matrices.
This generic algebra deliberately accepts the entry law and injectivity;
the physical consumer must supply R2 and the existing solver uniqueness,
respectively. It is not counted as either physical input or producer.
Text/import guard exit0/0.1317943s/12144640bytes observed peak RSS.
Text/import guards passed; no local Lean or new Colab was run for this draft.

## R4/R5 literal endpoint and measure conventions (static, not verified)

Re-read FinePointSourceHolomorphy at the normalized Green definition and
Eq249NormalizedStabilizedEndpointIntegralBound at the measure definition.
The integration parameter is NOT a unit cube: x belongs to [0,2*pi]^4,
physical momentum is x-pi, and the measure is the product of restricted
Lebesgue measures on uIoc 0 (2*pi). The outside normalization is (2*pi)^-4.
Thus the selected-coordinate reflection is x_mu -> 2*pi-x_mu, not 1-x_mu.
It preserves volume; no extra Jacobian or normalization is to be introduced.
The half-open interval reflects to the opposite half-open interval, so the
measure transport must account for null endpoints rather than assert exact
set invariance. This is distinct from the discrete alias permutation R1.

For R4 the physical endpoint reflection is S_N(t)_mu=N-1-t_mu, N=L^j.
The expected target exponential phase is D^-1 and the source phase is D;
their cancellation must be proved for the literal fine-to-fine integrand.
Wrapped phases vanish because both fine endpoints are integer-valued.
No analogous statement for arbitrary real endpoints is being assumed.
These are acceptance conditions for later proofs, not compiler evidence.

Existing R5 route located by reading signatures: Mathlib's
intervalIntegral.integral_comp_sub_left gives the slice reflection with
d=2*pi, a=0, b=2*pi. The sealed
integral_pi_restrict_uIoc_eq_of_coordinate_intervalIntegral_ae_eq lifts
slice equality to the product measure (cold source80c13cb97).
It requires integrability of BOTH product integrands; this must not become
a new free physical assumption. FinePointSourceHolomorphy already provides
integrable_cmp89Eq246PhysicalFineToFineGreenIntegrand_real; the newer
mass-uniform contour module is the candidate for avoiding a mass-positive
restriction. The reflected integrand's integrability still needs explicit
transport or a continuity proof. Hence R5 has a named finite route, not yet
a completed proof, and the half-open endpoint issue can be handled by the
existing interval integral theorem rather than a fresh set identity.

R2 status update (ledger1188/1189): v1 failed only at the positive-coordinate
simplification retaining if True; phase was not run. The one-line simp
repair passed carry and phase on the retained graph,10 exact axiom blocks,
independently verified HOT. Thus the matrix conjugacy is no longer merely
static, but remains unpromoted scratch; no actual Green reflection follows
until R3-R5. The original failed package is retained with its nonzero exit.

R3 HOT verified1191: literal matrix action and transport of the internally
constructed full solution both compile with the exact allowed trio. The
domain gates are the existing base/reflected FullSolutionDomain, not a new
uniqueness assumption. This does NOT identify the transformed arbitrary
source with the reflected physical point-source vector: that is precisely
R4, followed by target phase cancellation and R5 integral transport.

R4 endpoint phase substep HOT verified1192: integer reflection involution,
exact physical phase difference, target D^-1 and source D all compile.
The period cancellation consumes integer endpoints and explicit N^-1;
it is not a generic real-endpoint identity. Next identify the reflected
literal point-source vector with R3's constructed transport, then cancel
the target phase in the finite alias sum. Neither that consumer nor R5
is closed by these four phase declarations. Production promotion remains open.
