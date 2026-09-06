# After hRpoly: physical reconstruction and the continuum boundary

**6 September 2026. Status: static source audit and mathematical work plan.**
No new Lean build, oracle run, physical estimate, or frontier retirement is
claimed. The elementary arguments below are written proofs, not new
compiler-verified declarations or research novelty claims.

Main source inspected: `ff9498df9bb13050a3c663103e4a0830e793c56f`.
PR #29 completion checklist inspected at
[`7d773cd4a335f13c3946353f0ab5cb7bb47ca0f9`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/7d773cd4a335f13c3946353f0ab5cb7bb47ca0f9/docs/HRPOLY-END-TO-END-DOD-CHECKLIST.md).
Branch state may advance after this audit. Its fixed checklist is stronger
evidence for completion requirements than a moving PR description.

## What closing hRpoly actually supplies

The inspected checklist still records **20/41 terminal producers**,
**zero TermSource inhabitants**, and **physical window 15 not attained**.
Its progress annotation records newer selective cold checks through Addendum
1124; these do not retire the uniform physical `B0, delta0` obligation.
The proper regional inverse/reflection identification and derivative bounds
remain open. These are reported records, not independently reproduced here.

The terminal application in that checklist must produce physical
`SingleScaleUVDecay` and feed it into
`lattice_mass_gap_of_singleScaleUVDecay_marginal`. It explicitly permits
independent marginal-flow and IR hypotheses to remain.

The [consumer signature](../YangMills/RG/MarginalUVMassGap.lean) confirms this:
besides `hUV`, it takes positivity/smallness of `g`, the exact recursion
`g (k+1) = g k * (1 - beta * g k)`, exponent and rate conditions, and
`hIRbound`. Its conclusion bounds `covIR + covUV_concrete`. Thus removal of
`hUV` is not, by itself, an unconditional construction of a physical quantum
theory. A physical application must identify those objects and discharge or
justify the remaining inputs for the *same* model and parameter regime.
Existence of an abstract logistic sequence does not identify the physical RG
coupling. A known strong-coupling IR theorem cannot be substituted into an
unidentified blocked measure solely because the formulas look alike.

This does not establish that the proposed route fails. It specifies the
remaining application audit after a successful source estimate.

## Reuse the work already present

| Existing source | What can be reused | Boundary to retain |
|---|---|---|
| `L1_GibbsMeasure/IntegerThermodynamicLimit.lean` | Infinite-volume local state on integer coordinates; translation invariance; passage of eventual correlation bounds | The lattice spacing and the `UniformLocalKPRegime` are fixed. This is not removal of the ultraviolet regulator. |
| `L1_GibbsMeasure/ThermodynamicNonvacuity.lean` | Explicit SU(2), including d=4, strong-coupling instances and a nonconstant plaquette energy | Nonempty finite-spacing data do not prove a nontrivial continuum limit. |
| `L1_GibbsMeasure/ThermodynamicCorrelation.lean` | Two-plaquette clustering passes to the constructed state under the stated geometry and smallness conditions | One observable channel does not constitute a total family in a reconstructed physical Hilbert space. |
| `OS/SharpBridge.lean` | `sharp_clustering_iff_gap` and `volumeUniform_sharp_gap`, over complex Hilbert spaces | `VacuumTransferC`, a dense spanning family and matrix-element identification must come from the physical model. |
| `OS/SU2WilsonReflectionEndpoint.lean` | Complex Haar-kernel positivity and a sharp trace lower bound in the auxiliary SU(2) cut | Its scope warning explicitly says that the `Cross` variable does not enter the weight. No physical lattice plaquette factorization is supplied. |
| `OS/SpatialOS.lean` | A reflected Gibbs pairing for a finite binary-state bond chain | This is not four-dimensional SU(N) lattice Yang--Mills reconstruction. |
| `Paper/GapRefinementChallenge.lean` | Formal separation of stagewise and regulator-uniform gaps | Do not duplicate this quantifier lemma or relabel it a physical mass estimate. |

These are source-level findings. The exact recorded build and oracle scope
must be checked before promoting any combination to a verified endpoint.

Two common overstatements should therefore be avoided: "no thermodynamic
limit exists in the repository" and "the repository already reconstructs
continuum Yang--Mills because it has an OS directory".

## The independent workstream with the clearest physical use

**Construct the physical reflection/transfer bridge at fixed spacing.**
This work does not require waiting for hRpoly's Green-kernel estimates.
Start with one explicitly specified finite SU(2) Wilson lattice and a legal
reflection cut; general SU(N) and the volume limit are later extensions.

The first reviewable milestone should contain all of the following:

1. An actual involution on oriented lattice edges and configurations,
   together with the Haar product-measure invariance proof.
2. A split of the genuine Wilson plaquette factors into the two halves and
   crossing factors. Every crossing variable must occur with its actual
   orientation and weight; the auxiliary cut cannot stand in for this step.
3. Identification of the resulting form with
   `E_Gibbs[conj(F o theta) * G]`, with normalization and all integrability
   inputs proved for the specified finite model.
4. Positivity of the complex Gram matrix for arbitrary finite families of
   positive-time observables, and a concrete nonzero test observable.

This is a bounded formalization target, not a claim that its Lean proof is
already available or a forecast of its duration. It should be accepted by
its physical integral identity and oracle evidence, not by the number of
new interfaces. Merely adding a structure field containing reflection
positivity would not complete it.

Subsequent milestones: quotient by the null form, completion, a positive
transfer operator and vacuum, physical correlation/matrix-element identity,
and a dense family of local gauge-invariant observables whose clustering
can be supplied to `SharpBridge`. The existing two-plaquette estimate must
be extended to the necessary family or supplemented by an appropriate
cyclicity argument; it cannot simply be called dense.

**Do not impose an unnecessary constant-uniformity requirement.**
`SharpBridge` already permits a separate finite clustering constant for
each observable, and even for each volume in `volumeUniform_sharp_gap`.
What is common there is the exponential rate. Uniformity in the regulator
for a chosen continuum observable is a different question from uniformity
over all observables at a fixed regulator.

The canonical physical gate in
`RG/ConcreteGaugeRGPhysicalGate.lean` also has a distinct scope: the source
signature controls one canonical correlator at `2^n * u`, with `n >= 1`
and `4*u <= M0`. `ConcreteGaugeRGSupport.lean` explicitly leaves extension
beyond those separations and the continuum open. Such data are not
automatically the total physical family required by `SharpBridge`.

## A precise continuum handoff, with elementary proofs

The following sufficient criteria are useful specifications for a future
formalization. They construct neither Yang--Mills Schwinger functions nor
their convergence. For field theory, use properly normalized smeared
observables; pointwise field values need not exist.

Let `a_j > 0` tend to zero along a physically identified scaling trajectory.
Let `F_j(x)` be a renormalized connected correlation at physical separation
`x >= 0`, with a specified lattice approximation to that observable. The
field normalization and any approximation error belong to the data, not
to an adjustable definition of the desired answer.

### 1. Exponential bounds survive a known limit

Suppose, for each fixed `x`, that `F_j(x) -> F(x)` and eventually

`|F_j(x)| <= C exp(-m_j x/a_j) + e_j(x)`,

where `C >= 0` is independent of `j` for this observable,
`m_j/a_j >= m0 > 0` eventually, and `e_j(x) -> 0` with `e_j(x) >= 0`.
Then

`|F(x)| <= C exp(-m0 x)`.

Proof: since `x >= 0`, the rate comparison makes the right exponential no
larger than `exp(-m0 x)`. Pass to the limit using continuity of absolute
value and the closedness of the order relation. The eventual index may
depend on `x`; the constants `C,m0` do not. For a family of observables,
`C` may depend on the observable, while the desired spectral rate remains
common. This is a sufficient correlation-limit criterion, not a necessary
condition for every possible spectral convergence argument.

An unsmeared lattice estimate cannot be inserted unchanged if the selected
renormalization multiplies its prefactor by a diverging factor. That factor
must be accounted for in the displayed bound or controlled by another
argument.

### 2. Reflection positivity survives convergence of identified pairings

For any finite collection of positive-time smeared observables, suppose its
physical reflected matrices `K_j` are Hermitian positive semidefinite and
converge entry by entry to the matrix `K` of the limiting functional.
Then `K` is positive semidefinite.

Proof: for every fixed complex coefficient vector `z`, the finite sum
`z* K_j z` converges to `z* K z`. Each sum is real and nonnegative, and
the nonnegative real axis is closed. Hermitian symmetry also passes entry
by entry to the limit. This proves positivity of the limiting form once
its existence and identification have been supplied. It does not prove
the other OS axioms or the existence of the continuum functional.

### 3. A separate witness prevents collapse of the chosen sector

If, in addition to convergence, one identified connected pairing satisfies
`|F_j(x0)| >= c > 0` eventually, then `|F(x0)| >= c` by continuity.
For nontriviality of the OS quotient, use a centered observable with a
strict positive lower bound on its *reflected norm* and convergence of
that norm. This supplies a non-vacuum vector after the quotient.

Neither witness proves that the limiting theory is interacting or that
it is the required Yang--Mills theory. Those identifications remain separate.

### Why the additional data are necessary to the proposed inference

Take `a_j = 1/(j+1)` and the two-dimensional transfer operator
`T_j = diag(1, exp(-a_j^2))`. Each stage has a nonzero excitation and
positive dimensionless gap `a_j^2`. Its physical Hamiltonian
`-log(T_j)/a_j` has excitation energy `a_j -> 0`. Equivalently, the
connected spectral amplitude at physical time `x` is `exp(-a_j*x) -> 1`.
A positive gap at every lattice stage alone proves no positive continuum
gap. This is an abstract counterexample to that inference, not a
Yang--Mills counterexample.

Conversely, `F_j(x) = a_j exp(-m0*x)` has a common positive decay rate and
is nonzero at every stage, but tends to zero identically. Upper bounds
alone do not ensure survival of a nontrivial continuum observable. This
example is not a claim about every observable of a constructed theory.

## Remaining distance to the Millennium statement

The [official Jaffe--Witten problem](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf)
requires a nontrivial quantum Yang--Mills theory on R4, a positive mass gap,
and the stated axiomatic strength, for every compact simple gauge group.
The work above does not establish that statement.

The unresolved items along this programme include the physical hRpoly
producer and its matched terminal inputs; physical reflection/transfer
construction; a scaling limit with ultraviolet regularity and consistent
renormalized observables; continuum symmetries and reconstruction; survival
of a nontrivial sector and a positive physical spectral gap; and the
required gauge-group scope. Some operations may be reordered, but the
obligations cannot be removed by renaming a lattice decay rate.

No percentage or deadline for this mathematics follows from `20/41`,
the absence of project axioms, or a build-job count. The historical
`~0% (<0.1%)` label is a communication convention, not a calibrated
distance. The defensible assessment is: substantial reusable lattice
formalization, an open physical UV estimate, and major continuum
obligations still unresolved. hRpoly closure would be a meaningful
milestone; it would not make the remaining Clay proof a mechanical step.

## Validation and publication scope of this note

Static reads checked the named signatures, their stated scope, main imports,
and the fixed PR checklist. No Lean files, proof counters, canonical state,
or axiom transcripts are changed. No new mathematical verification is
claimed. Before any proposed lemma is promoted to a recorded core result,
it needs the relevant build and oracle checks on the sanctioned Colab
Linux plane, plus the repository's required evidence and review.
