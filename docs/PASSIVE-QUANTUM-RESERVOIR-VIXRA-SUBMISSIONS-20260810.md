# Passive quantum reservoir paper — viXra submission records

Date recorded: **2026-08-10**

Owner-reported operation: **two paper objects sent as new viXra submissions**

Moderation/publication outcomes and viXra identifiers: **not recorded here**

## Shared paper identity

Title entered for the current submission:

*Architecture-Dependent Decoherence Suppression in Passive Quantum Networks:
Irreducible Channel Mixing, Squared Rate Gaps, and the Price in Dwell Time*

- Author: **Lluis Eriksson**
- Primary category: **Quantum Physics**
- Secondary category, if accepted by the form: **Mathematical Physics**
- Public code and verification branch:
  [`research/quantum-reservoir-boundary`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/tree/research/quantum-reservoir-boundary)
- Research PR: [finite-sample-spectral-certificates #3](https://github.com/lluiseriksson/finite-sample-spectral-certificates/pull/3)

Both PDFs display the full title and `Lluis Eriksson` on their first page. Their
embedded PDF metadata uses the shorter main title *Architecture-Dependent
Decoherence Suppression in Passive Quantum Networks*; this record preserves
that distinction rather than treating the metadata title as the form title.

## Submitted object 1 — release v1.0

- Immutable release:
  [`v1.0-passive-quantum-reservoir`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/tag/v1.0-passive-quantum-reservoir)
- Release commit: [`b9df547eb6598342d182451e3ca7563458f48a70`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/commit/b9df547eb6598342d182451e3ca7563458f48a70)
- [Exact PDF](https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/download/v1.0-passive-quantum-reservoir/architecture_dependent_decoherence.pdf)
- Pages: **13**
- Bytes: **442,280**
- SHA-256: `4113C20A42D19F8018F7B8874B22E0F96AE594347AE5FDC7255B86FDF5EA9BDD`
- GitHub release publication time: **2026-08-10 03:09:03 UTC**

The v1.0 release packages the explicit passive six-port construction, exact
architecture separation, squared Kossakowski-rate separation, delay-resource
bound, exact no-go and numerical stress tests. Its GitHub release is public;
that fact is separate from viXra moderation.

## Submitted object 2 — release v1.1 robustness hardening

- Immutable release:
  [`v1.1-passive-quantum-reservoir`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/tag/v1.1-passive-quantum-reservoir)
- Release/source commit: [`4bb63290ea4da5c914a4d8eaed7b71a49fa3678f`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/commit/4bb63290ea4da5c914a4d8eaed7b71a49fa3678f)
- [Exact PDF](https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/download/v1.1-passive-quantum-reservoir/architecture_dependent_decoherence.pdf)
- Pages: **17**
- Bytes: **506,639**
- SHA-256: `B4DDFCC82B3B0C8B620F5A786083B0B951380B220D582FA3F51FF6D5C303F9D2`
- GitHub release publication time: **2026-08-10 04:01:24 UTC**

GitHub's release API reports the same sizes and SHA-256 digests for both assets.
The page counts, displayed title, author and digests were also independently
recomputed from the downloaded release PDFs.

## Exact v1.1 submission metadata

Keywords:

> passive quantum networks; decoherence suppression; reservoir engineering;
> irreducible channel mixing; Schur transfer functions; Blaschke products;
> Kossakowski matrices; quantum filtering; Ramsey dephasing; robustness; group
> delay; dwell time

Comments:

> 17 pages, 4 figures, 2 tables. Includes an explicit passive six-port
> realization, a quantitative finite-error obstruction theorem, an exponential
> no-uniform-robustness theorem, a vacuum-complete Ramsey model, multiprecision
> certificates and a delay-resource bound. Source code, frozen numerical
> ledgers and verification workflows are publicly available.

Abstract:

> We study whether passive reservoir filtering can suppress decoherence more
> effectively when its channel mixing is irreducible, even after fixing the
> passband responses and rational complexity. For every integer S >= 5, we
> construct an explicit causal inner six-port network with three signal and
> three vacuum-loss ports. Its signal block is a rational Schur transfer
> satisfying 3(S-1) delayed full-spark tangential calibrations and exhibiting
> exponentially small leakage on two stop arcs. In contrast, every transfer of
> the same bidegree possessing a constant nontrivial reducing channel and
> satisfying the same calibrations retains unit stopband norm.
>
> We strengthen this exact separation with a quantitative finite-error
> obstruction: for calibration defect delta and sampled reducing-line defect
> beta, comparator leakage is bounded below by [1-C_S(delta+beta)]_+, with C_S
> given explicitly by finite singular-value margins. A scalar Schur
> construction proves that every bound of this form must deteriorate at least
> as 2 exp(9S/20)(1+o(1)); hence uniform robustness is impossible for the chosen
> clustered calibrations.
>
> For uniformly nondegenerate bath spectra, the signal-level separation is
> squared at the Kossakowski-rate level. A closed Markov pure-dephasing model
> includes all auxiliary vacuum ports exactly, producing an
> architecture-independent measurable baseline and an explicit total
> Ramsey-rate advantage. Finally, we prove that strong passive suppression
> requires large dwell time: under a peak-delay budget D, the rate-improvement
> factor is asymptotically at most quadratic in D/S. The construction therefore
> moves the coherence-maintenance resource into passive memory, vacuum noise
> and conditioning rather than eliminating it. All certificates, figures and
> numerical audits are publicly reproducible.

The recommended AI-assistance declaration attributes mathematical exploration,
numerical implementation, verification tooling and drafting assistance to
Codex under the author's direction and final supervision. Journal reference,
DOI and report number were intentionally left blank.

## Scope and lifecycle

The public GitHub releases are immutable evidence objects. This record does not
turn the stated provisional internal evaluations into external peer review and
does not infer viXra acceptance from release publication. Until identifiers are
reported, both viXra objects remain recorded as **submitted / pending outcome**.

The v1.1 release is the later, robustness-hardened object and is therefore the
one exposed as `latest_submission` in the repository dashboard. The v1.0 object
remains independently addressable by its own tag, commit, size and digest.
