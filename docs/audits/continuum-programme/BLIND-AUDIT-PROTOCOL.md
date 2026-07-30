# Blind audit protocol: SU2 / OS / continuum

Status: **REGISTERED**  
Registration date: 2026-07-30 (Europe/Stockholm)  
Repository: `https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME`  
Public comparison base: `origin/main` at
`7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`  
Audit branch: `codex/continuum-source-audit`

Baseline supersession: the initially registered base
`81721890ad3e111d73cbe45074d42ec698ce07b2` was superseded on 2026-07-30
after a fresh `git fetch origin main` showed that public `main` had advanced
by one commit to `7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`.
The intervening commit adds `papers/spatial-os/spatial_os.{tex,pdf}`. The old
base and this correction remain in Git history; no claim is silently moved
between them.

## 1. Independence and order of operations

This desk does not produce proofs for hRpoly, Paper 13, SU2-OS,
Continuum-C0, or Continuum-C1. It tests their public artefacts from a clean
checkout at an exact commit.

The tests below were fixed before reading any producer conclusion or prior
auditor verdict that could determine their outcome. Repository-wide standing
instructions and live-state files were read only to identify scope,
prohibitions, and claimed interfaces. Later source packets must distinguish
facts independently recovered from primary sources from claims merely reported
by this repository.

No absence of a counterexample is evidence of a proof. A formal theorem is
credited only for its literal statement and hypotheses. A mathematical paper is
credited only for the claim actually established under its stated assumptions.

## 2. Claims to be tested

### SU2: finite-lattice reflection positivity

SU2-1. The chosen lattice, reflection plane, positive-time algebra, boundary
links/plaquettes, orientation convention, and action are specified.

SU2-2. The Wilson Boltzmann weight admits the claimed reflected splitting:
a positive-side factor times its reflected/conjugated factor times crossing
terms having a positive-semidefinite coefficient kernel.

SU2-2G (gluing gate). If the artefact defines its reflected form by summing
over pairs of half-configurations, it proves that the two halves, their shared
or boundary variables, the crossing factor, and product Haar measure assemble
the original full-lattice Gibbs integral exactly. The proof must include the
actual measure-preserving reindexing/factorisation and all boundary
normalisations. A finite `Z_2` brute-force check, analogy, or citation does not
establish this identity for continuous `SU(2)`. If instead the artefact treats
only real observables of one time slice, it may receive credit for exactly that
restricted statement but fails any advertised full OS-positivity or
reconstruction claim.

SU2-3. Every use of Haar integration, Peter--Weyl orthogonality, characters,
matrix coefficients, representation dimensions, and Wilson coupling uses one
explicit normalization consistently.

SU2-4. Reflection includes all required link inversion, path-order reversal,
matrix conjugation/adjoint, and complex conjugation. The asserted quadratic
form is real and nonnegative for arbitrary finite linear combinations of
positive-side observables, not merely for one diagonal or endpoint observable.

SU2-5. Character/matrix-coefficient expansion coefficients have the asserted
sign and convergence properties at the stated coupling. Boundary and crossing
plaquettes are neither omitted nor double counted.

### OS: reconstruction

OS-1. The exact reconstruction target is identified: finite-lattice transfer
operator, infinite-volume lattice Hilbert space, Euclidean continuum OS
reconstruction, or Wightman theory. These targets are not interchanged.

OS-2. The full hypotheses used by the cited reconstruction theorem are stated
and matched one by one (domain/algebra, Euclidean covariance or the relevant
lattice subgroup, reflection positivity, regularity/continuity or growth,
symmetry, cluster/ergodicity where invoked, and the required compatibility of
Schwinger functions).

OS-3. The null-space quotient, completion, time translations, contraction or
semigroup property, self-adjoint generator, vacuum, fields/distributions, and
spectral statements are constructed only to the extent licensed by the matched
hypotheses.

OS-4. A positive mass gap is not inferred from reflection positivity alone.
Any gap statement identifies the operator, Hilbert space, vacuum sector,
uniformity, units, and relation to connected correlations.

### CONT-C0: existence of a continuum candidate

The `CONT-` prefix is mandatory in reports and manifests. It avoids collision
with the repository's pre-existing paper-lane charters `C1` through `C6`.

CONT-C0-1. The regulator family is explicit: lattice spacing `a`, physical volume,
boundary conditions, bare/renormalized parameters, gauge fixing or
gauge-invariant observables, and the directed order (or joint manner) of
limits.

CONT-C0-2. A claimed limit is not an arbitrary selected functional, definition by
the desired answer, constant family, or limit theorem whose hypotheses already
encode convergence to that same answer.

CONT-C0-3. Tightness/precompactness or an equally strong construction is proved in
a topology that supports the claimed observables/distributions. Subsequence
existence, uniqueness, and full-family convergence are kept distinct.

CONT-C0-4. The candidate has a physical scale and is nontrivial. Normalization,
renormalization, and the possibility of a Gaussian, zero, ultralocal, or
otherwise degenerate limit are addressed rather than assumed away.

### CONT-C1: uniform continuum control

CONT-C1-1. Every constant is traced through dependence on lattice spacing, lattice
extent/physical volume, ultraviolet cutoff, infrared regulator, coupling,
observable support, and renormalization scale.

CONT-C1-2. Dimensions and units balance before and after rescaling. A lattice-unit
gap or correlation length is not called a positive physical mass without the
required `a`-scaling.

CONT-C1-3. Bounds used for compactness, removal of cutoffs, clustering, or a mass
gap are uniform in exactly the regulators subsequently removed.

CONT-C1-4. No circular input appears under a renamed interface: the continuum
limit, nontriviality, a uniform physical gap, OS axioms, or the desired
renormalized estimates may not be hypotheses of a theorem advertised as
proving that item.

### Clay comparison

CLAY-1. The exact official Yang--Mills existence and mass-gap statement and its
official exposition are quoted or paraphrased with a direct authoritative
locator.

CLAY-2. The audit maps the repository artefact to the official requirements:
four-dimensional non-abelian compact simple gauge group, existence on
`R^4`, axiomatic strength at least as strong as the cited requirements, and a
strictly positive mass gap independent of finite-volume and ultraviolet
regulators.

CLAY-3. Finite-lattice RP, a thermodynamic limit at fixed lattice spacing, a
lattice-unit spectral gap, conditional reconstruction, or a formal implication
with substantive hypotheses is explicitly marked insufficient for CLAY-2.

## 3. Required evidence

Each credited external technical claim requires:

1. a primary or authoritative source with stable URL and DOI when available;
2. exact page, section, equation, proposition, or theorem locator;
3. the hypotheses in the source's own mathematical setting;
4. the conclusion, without strengthening by paraphrase;
5. an applicability map to the exact producer object; and
6. a discrepancy entry for every unmatched hypothesis, convention, or target.

Each credited repository claim additionally requires:

1. immutable commit SHA and file path;
2. literal theorem/definition text or paper statement;
3. dependency and hypothesis inventory;
4. reproducible commands from a clean public checkout;
5. tool versions, command exit status, and hashes of load-bearing inputs and
   transcripts; and
6. a witness for every failure that can be made finite and inspectable.

Secondary press, encyclopedia summaries, search-result snippets, and uncited
model output cannot support technical conclusions.

## 4. Verdicts

The unit of judgment is one registered claim, never a whole programme by
association.

- **PASS**: all required evidence is present; the clean-checkout test succeeds;
  every load-bearing hypothesis and normalization is matched; and no registered
  adversarial test produces a counterexample.
- **FAIL (witness)**: a finite counterexample, inconsistent normalization,
  false identity, unit mismatch, non-uniform constant, circular dependency,
  clean-checkout failure, or literal statement weaker than the advertised claim
  is exhibited. The verdict records the smallest reproducible witness.
- **BLOCKED (missing datum)**: the claim cannot be decided because a named
  artefact, convention, dependency, source page, parameter range, hash, or
  executable instruction is absent or inaccessible. BLOCKED is not PASS and
  does not estimate truth.

Mixed bundles are split claim by claim. A successful build proves elaboration,
not the intended mathematics beyond the literal theorem statement.

## 5. Supersession and correction rules

1. Evidence is immutable by commit SHA. A later producer commit does not alter
   a verdict on an earlier SHA.
2. A new audit may supersede an earlier one only if it names both audit IDs,
   the new producer SHA, the changed evidence, and the claims reconsidered.
3. Textual renaming does not supersede a mathematical failure. The witness
   must be answered or the advertised claim narrowed.
4. A repaired claim receives a new clean-checkout run and verdict. It is not
   silently upgraded in place.
5. Source corrections retain the erroneous entry in a correction log and
   identify the authoritative replacement.
6. Later discovery of an unmatched hypothesis downgrades PASS to FAIL or
   BLOCKED in a new signed report; chronology is preserved.
7. Producer, source-desk, and independent-model outputs remain separately
   attributed. External-model suggestions never count as evidence until this
   desk verifies them against primary sources or executable artefacts.

## 6. Publication contract

Source packets, executable templates, run manifests, and verdicts live only
under `docs/audits/continuum-programme/` or in clearly isolated audit scripts.
This desk will not merge producer PRs or edit producer files, repository state,
ledgers, dashboards, the oracle, or `YangMillsCore`.

## 7. Baseline correction log

`BASELINE-20260730-01` — **CORRECTED, not erased.**

- Initial base: `81721890ad3e111d73cbe45074d42ec698ce07b2`.
- Authoritative recheck:
  `git fetch origin main --prune && git rev-parse origin/main`.
- Corrected base: `7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`.
- Changed material: commit `7c6aaab2`, adding the Paper 13 TeX/PDF.
- Provenance boundary: `YangMills/OS/SpatialOS.lean` and
  `scripts/judge_spatial_os.py` already exist at the old base; the Paper 13
  TeX/PDF do not. No assertion from the absent TeX/PDF is credited at the old
  SHA. The clean-checkout numerical run at the old SHA remains a run on that
  old artefact and will be labelled as such.

`BASELINE-20260731-02` — **SUPERSEDED CLAIM BY CLAIM.**

- New public main: `1e6113a10c407ba2964af2713aef26c62bbd1157`.
- Changed material: Paper 13 v1.1, its `SpatialOS` Gram declarations, and
  oracle coverage.
- Superseding report:
  `PAPER13-v1.1-AUDIT-20260731.md`.
- Effect: the bond finite-family Gram gap is closed and the coupling headline
  is narrowed to sufficiency. The half-to-whole-path assembly/gluing gap is
  unchanged. No earlier SHA-level transcript is rewritten.
