# A concrete Fourier cube, without an assumed dimension

This is a construction step toward the flat coarse-rank obstruction. It defines
actual functions on the finite torus `(Fin d -> ZMod n)` and their span, rather
than packaging a desired dimension into a hypothesis.

For a frequency vector k, the character is

    x |-> stdAddChar (sum_i k_i x_i).

Evaluating at each coordinate unit vector proves the frequency-to-character map
injective. Orthogonality/independence of finite-group characters from pinned
Mathlib then proves independence of these particular torus functions. Labels
`Fin (2*R+1)` become centered residues `-R,...,R`; the proof that `2*R<n`
prevents aliasing is supplied explicitly. The centered span therefore has
complex dimension `(2*R+1)^d`.

Restricting its scalars from complex to real gives dimension
`2*(2*R+1)^d`. These are **complex-valued profiles with two real internal
coordinates**, not real scalar profiles counted twice. In particular, the
conjugation constraint on real scalar Fourier coefficients has not been assumed
away. A later embedding into physical cochains must preserve this interpretation.

## Scope and next concrete obligation

The scalar functions, their independence, the span and its dimensions are
constructed. A low-energy subspace of physical positive-bond cochains is not yet
obtained from this alone. The internal-coordinate embedding, replication across
bond directions, norm comparison, actual Hodge action and energy bound remain
to be proved. The explicit lattice bound from the analytic note therefore
remains analytic at this stage.

The ambient function type here is used for algebraic dimension only. Its
default function-space norm must not be substituted for the counting-measure
L2 norm of physical cochains. A future energy proof must explicitly transport
the band to `WithLp 2`/`PiLp 2`, or prove the corresponding finite sums directly.

The abstract dimension obstruction already proved in
`CoarseMeasurementDimensionObstruction.lean` can be used only after these actual
cochain estimates are supplied. No hRpoly producer or physical spectral gap
follows from this character-space calculation. No standalone paper or novelty
claim is proposed: finite-torus character independence and the scalar tower law
are classical, with their pinned Mathlib implementations used here.

## Verification record

The source commit, two LF-normalized source hashes, pinned Lean/Mathlib versions,
target and four expected axiom reports are frozen before Colab execution. Logs
and any failed attempts are retained. A target build and focused oracle check
this construction only; they do not check the remaining physical embedding or
upgrade the analytic lattice endpoint to a formal result.

The first version passed its target build and four-report oracle without a
proof repair, at `b4359681d334b7695a18da0dba28401c85d70aae` (run012). Two
extra EOF blank lines introduced during file transport were then removed;
neither the mathematical source bodies nor the oracle criterion changed.
The clean source is frozen at `0e88dfe5f434123e057dd83c17801872fc2498a5`.

Run013 verified that exact clean source in a fresh Colab CPU/high-RAM clone:
all nine steps exited zero and the four reports contained exactly `propext`,
`Classical.choice`, and `Quot.sound`. It ran 16:56:58-17:00:14 UTC on
29 October 2026 and released the runtime after persistent evidence output.
Its complete evidence ZIP has SHA-256
`12118ffc8275d7d0269d70f33d2be9e406f1d5547d15b5a94f379d0f40cbc458`.
The target `.olean` has SHA-256
`a2b022a15072394e6b3722f9ad692cb1370c8a160013d5f1672f13863e4d485f`,
and raw `oracle.log` has SHA-256
`b53be8d889e03f2a0e96a44f2dda9c902133ea6653c0c51e7b4cde51a6afc3c8`.
Both hashes also match the initial run012, but the source SHA differs, so that
does not satisfy the two-fresh-clones-at-one-SHA requirement.

A second clean-source run014 was launched in its own CPU/high-RAM runtime.
Its browser tab stopped responding to documented control calls. A fresh tab
recovered only the five initial exit-zero steps saved in Drive; no final verdict
or complete ZIP was recovered. The session inventory subsequently showed no
active session (17:06 UTC). Do not treat that run as a pass, a measured Lean
failure, or a second complete reproduction. It remains an evidence limitation;
no additional runtime was opened merely to look for the missing output.

The complete run012 and run013 packages are preserved in the repository's
reproducibility folder. Only run013 is a complete package for the final clean
SHA. A second complete same-SHA reproduction is still required before terminal
reproduction closure. No GPU, Windows Lean/Lake or shared runtime was used.
Compute units were not measured. Separate execution sessions orchestrated in
this same chat are not independent scientific review.

### Same-SHA reproduction completed in unit012

On 29 October, the saved notebook014 was re-executed in a newly allocated own
CPU/high-RAM runtime. This new attempt is called **014b** in the archive; it
does not retroactively supply the missing verdict of the original attempt014.
Its report ran 17:40:29.037302-17:43:25.153860 UTC, with all nine steps exiting
zero and all four exact oracle reports matching the frozen criterion. The
runtime was released automatically; the reconnect control was then observed.
Compute units and pre-execution allocation duration were not measured.

Its complete ZIP has SHA-256
`c4f44751c26f6d232f9b139b860d40eae0d20fd25b18d1c6ed1e181432f16dee`.
The validator checked all twelve manifest entries, both source hashes, all
nine child exit codes and all four oracle reports. Source SHA, target `.olean`,
raw `oracle.log` and source-hash manifest match run013 exactly. Thus **013 and
014b now supply the two fresh-clone packages at the final source SHA**
`0e88dfe5f434123e057dd83c17801872fc2498a5`. The earlier reproduction limitation
is resolved for this module only. The original partial014 remains a recorded
transport failure with no recovered verdict. No mathematics or judge changed.

This closure concerns the concrete character-space dimension, not the cochain
L2 embedding, Hodge energy, the whole repository or an independent review.
The analytic fixed-map repair criterion and explicit two-dimensional falsifier
are recorded separately in `FIXED-MEASUREMENT-REPAIR-CRITERION-20261029.md`.
