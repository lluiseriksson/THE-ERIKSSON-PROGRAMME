# Exact physical-interface flat Hodge energy of a Fourier component

This continues the existing rank-obstruction dossier. It identifies the actual
flat repository Hodge form, not an assumed scalar replacement. Let E_j f be
the previously constructed real one-component embedding of a complex torus
profile into two Euclidean internal coordinates. For n>0, d>0, Nc>=2 and an
admitted SUNAdjointModel at the explicitly trivial background, the proved identity is

    <E_j f, K0 E_j f> = sum_{i != j} forwardEnergy_i(f) + backwardEnergy_j(f).

The source constructs this identity from the actual curl and divergence.
`gaugeConstraintQCLM` is the divergence in this operator identity; it is not
the arbitrary coarse measurement map C in the separate rank obstruction.
The pointwise curl is supported on plaquettes containing j. A plaquette has
ordered coordinates a<b (one representative of each unoriented pair). Its
contribution is the i-th forward difference, with a possible overall minus
sign, when {a,b}={i,j}. The two cases are disjoint because a<b. The finite
incident-pair sum is proved for an arbitrary real function F; no positivity,
orthogonality, Hodge identity or count is supplied as a hypothesis. This is
where an erroneous factor of two must be excluded.

Reindexing by actual sites and their FinBox/ZMod equivalence gives the exact
curl norm sum. Adding the already verified divergence norm then identifies
the actual Hodge form with `oneComponentStencilEnergy`. For every concrete
centered Fourier synthesis with 2R<n, the previously derived scalar estimate
and the proved physical counting norm give the proved bound

    <A,K0 A> <= (4*pi^2*d*R^2/n^2) * ||A||^2.

The exact theorem and its proof status must be read from the verification
record below. This is an upper bound on a finite flat low-mode family. It is
not a positive spectral-gap theorem or a Yang--Mills continuum construction.
“Physical” means the repository's Euclidean-coordinate cochain interface,
not an additional identification with a matrix Lie algebra. No nontrivial
background, potential V, full q-fold band or continuum limit is included.
Nc>=2 ensures the internal real/imaginary coordinates exist. Choosing j:Fin d
ensures d is nonzero; the operator API uses that explicit instance.

## Verification

Tested source17733eebb779fae4aa1aecc9cdfab8f6d4133c07 passed on its first
candidate in two fresh, serial Colab CPU/high-RAM clones. Both complete ZIPs
were recovered and locally validated:12manifest entries,2source hashes,
9exit-zero steps and5named oracle reports, each using exactly propext,
Classical.choice and Quot.sound. Source SHA, target .olean, raw oracle.log and
source-hash-manifest digests agree between the two clones. Each run also
accepts the positive oracle log and rejects3mutations of actual log fields
in both normal and optimized(-O) Python. No acceptance depends on assert.

| Artifact | SHA256 of raw bytes |
| --- | --- |
| run029.zip | 458841c34be7b8e745ee2d842d435c3192895b5100f36d6b0156ee4db814b74f |
| run029b.zip | 89431cc7370f2b522991730af8b322ed43b050672ef4feab888d0406ab6935e8 |
| target .olean, both | 09ecc509d808cf74c934e1a3b61138c81b96a671e5f7ed4acea92cfa6ee08050 |
| oracle.log, both | 9f6b040545ea377ad1c41ae6cae58f665bf4fa1f55ec86b38239ab1eadfc576a |
| source-hashes.json, both | 084435fe958d9f74f3e527db253b9e99ed8d926ca6505f2c8011ad560485967a |

Normalized LF source SHA256:
moduleb7c42c95203a9171fe9b6c4c875d5e5b3149e03f56104d92281a668c039792ac;
oracle3b9f84eab6b04bdbee1207e97ee5838d34c6d82314a260183b59e6ca79d47acb.
Only source LF hashes use normalization; ZIPs and compiled/raw log digests do not.
The five theorem declarations are orderedDirectionPair_incident_sum,
torusPhysicalEmbed_flat_curl_norm_point,torusPhysicalEmbed_flat_curl_norm_sq,
torusPhysicalEmbed_flat_hodge_eq_stencil,centeredFourier_physical_hodge_le.

Run029:00:38:09.470823-00:43:23.442304UTC30October2026,313.971481s;
run029b:00:44:45.090758-00:49:13.526324UTC,268.435566s. Total execution
intervals582.407047s. Both automatically released and disconnected controls
were observed;50.99GB RAM observed. Allocation/release overhead and compute
units were not measured. No GPU, new purchase, shared runtime or local
Windows Lean/Lake. No failed Lean attempt or proof repair occurred in this
unit. Scoped elaboration allowances are800000heartbeats for auxiliary/bridge
declarations and1500000for the curl sum; these are resource limits, not
hypotheses or kernel-checking exceptions.

PR93 was merged only after both required checks succeeded at1971409, by
merge54adb99a03ba9c71f6016f6fcfc56ba510a26ff6. During reproduction the working
branch incorporated that main by mergef245b0617cf1ebe6dd0f167188717c7c38ec50f5;
an explicit git tree comparison with the tested17733ee was empty. The tested
source remains an ancestor of the final head; no rebase or squash is used.
The earlier parent PR93 source is not rebuilt as a separate research result.

Full packages, validations, runtime intervals, exact executed notebook and
normal/-O selftest code are in `reproducibility/torus-physical-hodge-20261030/`.
The convenience Python copy trims only excess EOF blank lines; the notebook
preserves the exact executed input. This is focal module reproduction, not
an independent scientific review or terminal audit of the entire repository.

## Sources and originality

These finite-difference and Hodge identities are classical. The contribution
here is a checked construction linking the previously proved scalar band
bound to the actual operator definitions; it is not a new independent paper.
The source reuses `concretePlaquetteEquivOrderedPair` from the existing
physical low-mode Hodge module rather than creating another lattice model.
Primary evidence: the tested repository SHA, the exact operator definitions
and their verified application formulas, and Mathlib's finite subtype sums
at pin07642720480157414db592fa85b626dafb71355b:
[finite sums over subtypes and filters](https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean).
A targeted primary-source check also found J. Dodziuk, *Finite-difference
approach to the Hodge theory of harmonic forms*, American Journal of
Mathematics98(1),79-104(1976), DOI10.2307/2373615:
[author's institutional record](https://academicworks.cuny.edu/gc_pubs/180/)
and [article text](https://www.maths.ed.ac.uk/~v1ranick/papers/dodziuk.pdf).
Its introduction and section4 place inner products on finite cochain spaces
within established combinatorial Hodge theory. This supports the historical
background only; it does not certify this repository's cubical normalization
or the particular formalization. The targeted search is not an exhaustive
priority audit, and no new general Hodge theorem is claimed here.
Formal correctness, originality and relevance remain separate assessments.

## Model assessments and review context

Construction and orchestration are by this chat's Codex assistant. The exact
backend identifier is not exposed in this run. Same-workflow Colab Lean checks
are mechanical reproductions, not independent scientific reviews, peer review,
model scores, acceptance or publication. No previous PDF assessment is
inherited. This internal code note creates no new AIRR/ai.viXra deposit or PDF.

## Next question and abandonment criterion

Once the energy identity is verified, construct the actual real linear image
of the centered synthesis, prove it is injective, and derive its real dimension
2*(2R+1)^d. Then the already proved abstract rank obstruction can be applied
to arbitrary measurement and repair maps with total dimension M+r smaller
than that value. This uses only the one-component two-real-coordinate range;
no q-fold dimension formula is asserted. The finite-volume scaling eta=1/L
must remain separate from the unit-spacing obstruction.

Falsifiers: duplicated plaquettes, wrong orientation sign, wrong L2 counting
normalization, wrong real dimension, or mixing physical spacing conventions.
Do not place any missing property into a structure. After three units with
no substantive mathematical advance, document the precise obstruction and
change route. PR29 remains20/41,TermSource=0; no hRpoly producer is discharged.
