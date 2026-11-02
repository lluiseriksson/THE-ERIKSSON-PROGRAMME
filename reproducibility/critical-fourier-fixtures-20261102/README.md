# Exact finite critical Fourier/flow diagnostics — own Colab109

Unit104,2026-11-02. This package checks finite adapters from critical-inverse-moment-spectral-threshold.md, not the general theorem, a new theorem, a physical mass gap or a Lean endpoint. Analytic source version:527fcdcd119a056e7ea188cd50e33421a663125d; integration main8e7eace214fd4f47a1d3d88de17ceefadc6828c3 also includes unit103's separate dyadic obstruction. No earlier source/PDF score is changed.

## Exact execution and results

The fixture source is pinned at4bb460e1537ed2f0bdc8b845b9c0304cfe3128c7, canonical LF SHA25611db01f92651edd6497f80ef28b3a4dd69c9a7ab90769f4edc00ff0e33462f45. Driver109 SHA2563880aae65d2ce2c8080a2a55f1be4ec6ab05a40cde26e759e26b7a931d954ff2 embeds those exact bytes and rejects any hash mismatch. The notebook contains a second byte/hash guard around that driver. The clipboard's CRLF line endings were normalized to LF before equality comparison; embedded bytes are unchanged.

Own Colab Linux CPU/high-RAM109 ran2026-11-02T17:13:06.300923Z–17:13:16.201862Z. Both normal and python-O children exited0, each accepting4 profiles and rejecting16 real mutations; their complete mathematical fixture outputs match. No decision to accept, increment an acceptance counter or report success uses Python assert. All mathematics ran in Colab, not Windows. No dependency install was needed: standard-library Fraction arithmetic throughout.

The runtime was requested17:12:52.311Z after preparing disconnected with0 active sessions. It auto-unassigned in finally;0 sessions and rate0 were visible after completion, observed no later than17:14:16.382Z. The request-to-observed-release interval is only an upper bound on connection time; the driver interval is the exact recorded execution interval. The retained own CPU/high-RAM configuration was used; COLAB_GPU was empty. Visible units1765.76 before/after are rounded; no zero-cost inference is made. The initial stale browser binding was recovered by ordinary controller reset without another-chat or native-Chrome access.

## Fixtures and independently useful identities

All profiles live on the actual forward-difference torus (Z/2Z)^4, with16 sites and critical inverse exponent2. The normalized real Walsh Fourier matrix has entries plus/minus1/4. Each profile has1<=a<=2m and actual arithmetic mean m. Results below count actual scalar eigenvalues strictly below c, including the single constant mode.

| Actual profile | m | mean((m/a)^2) | low counts at c=1/2,4,10,40 | inertia of sum(T_i*T_i)-L_a^+ |
|---|---|---|---|---|
| all1 |1|1|1,1,11,16|0positive,0negative,16zero|
| all4 |4|1|1,1,1,11|0positive,0negative,16zero|
| one1,other fifteen9 |17/2|289/54|1,1,1,5|4positive,0negative,12zero|
| parity-alternating1/4 |5/2|425/128|1,1,1,15|15positive,0negative,1zero|

The exact program constructs original incidence matrices, verifies the actual directed Fourier symbols, computes weighted inverses after adding/removing the constant projector, and verifies their mean-zero identities. Symmetric rational elimination determines inertia using scalar pivots and actual2x2 zero-diagonal pivots; a separate2x2 indefinite example and diagonal example are checked. Uniform profiles' multiplicities are also compared with the explicit Fourier eigenvalue list4*a*popcount(k). In particular the strict threshold c=4 excludes eigenvalues exactly4, rather than confusing < with <=.

For a fixed nonzero mean-zero rational source f it constructs the feasible flow dL0^+f and the minimizing flow a*dL_a^+f. It checks actual divergence=f, the zero orthogonal cross term and the exact excess-energy identity. The positive matrix comparison L_a^+<=sum(T_i*T_i) is checked by exact inertia on the full space with the constant kernel retained. The two heterogeneous profiles make the comparison nontrivial; uniform profiles give exact equality.

For each of four directional symbols it computes the normalized finite weak-frequency quantity directly and checks the proved safe bound(3/4)^4. For each profile it checks12 actual density examples: gamma=A/2 and two nonuniform rank-one gamma=A*v*v*A/(v*A*v), for each of four A=Fourier*diag(g_i^2)*Fourier. Positivity, gamma<=A, the pseudoinverse trace and the p=2 density lower bound are checked exactly. This is48 examples in each mode, not a proof for every gamma.

For four c thresholds it checks weighted inverse/low-spectrum multiplicities, noncommuting positive-sum min-max counts, component finite Cwikel bounds and the resulting scalar low-count bound. Constants are deliberately safe and some finite bounds are loose or vacuous; passing them does not establish asymptotic sharpness. The complete counts and rational bounds are in both stdout files and the report.

Each valid profile is then copied and changed in four REAL places: an actual weighted Laplacian entry, an actual weighted inverse entry, a feasible-flow coordinate, and the comparison-sum matrix. Each altered input must be rejected by the verifier; all16 were rejected per mode. These mutations exercise exact structural and mathematical checks. They do not prove soundness against an adversary replacing the whole package or supplying an entirely different dataset.

## Full reproducible evidence and limits

109-full-evidence.zip SHA2561c433591db41963cc76d9fa3b4cfdf587f314649fd19fc263010016b76d54ec8 contains9 entries:8 files listed by the inner manifest, plus that manifest. Every inner listed file was rehashed after extraction on D; all matched. The executed fixture and driver hashes match the frozen source and recipe. Full normal/optimized stdout, stderr, report, Python/platform record, recipe and fixture bytes are retained, not just a PASS summary. 109-validation.json records each file hash check. Local operations were editing, git, hashes, archive transport and JSON metadata; no local mathematics/build/oracle.

This is ONE finite diagnostic batch from embedded SHA-pinned bytes. It is not the repository's two-fresh-clone terminal reproduction criterion, a new Lean/kernel proof, a general proof of the endpoint, independent mathematical review or an exact-PDF evaluation. It tests dimension4,n2 and p2; odd side lengths, arbitrary dimensions/exponents, the full density family, general field-index formal adapters and continuum/interacting operators remain outside this batch. The actual mathematical novelty context remains the classical Rumin/Frank method credited in the analytic note (primary arXiv1206.3325v1,section2); no new mathematical novelty is asserted for these fixtures.

## Model assessments and review context

FIRST exact diagnostic-package self-assessment5/10 by the same preparing Codex agent. Actual served backend identity and effort unexposed. Rubric0-10: exact fixture implementation7, mathematical coverage4, novelty1, dossier verification relevance7; overall5 is qualitative, not an average or calibrated probability. No independent review, peer review, editorial acceptance, inherited score or grade-seeking repetition. The endpoint analytic note's first6/10 and the dyadic note's first5/10 remain unchanged.

O1. Finite rational PASS cannot certify the general analytic theorem or replace Lean formalization.

O2. Four small profiles and48 density examples per mode do not cover arbitrary n,D,p,coefficients or gamma; no asymptotic/odd-grid claim follows.

O3. Exact inertia is an authored algorithm, not a trusted kernel; limited independent checks are2x2/diagonal cases and uniform Fourier multiplicities.

O4. Some counting bounds are loose at this size. Matrix/flow mutation rejection is meaningful but not an adversarial certificate-security theorem.

O5. One embedded-source execution batch is not two fresh matching clones and is not independent model review. UI recovery and rounded resource observations are recorded with their limits.

O6. This package contributes verification of existing results, no new mathematical theorem or resolution of the unrestricted rectangular endpoint. That remains the ONE active research question; full cube trees were eliminated by unit103, not by these tests.

O7. No physical interacting/continuum gap, new small paper, PDF/AIRR deposit/acceptance/publication or PR29 progress. PR29 remains20/41,TermSource=0. All earlier exact-version permissions and assessments stay attached to their own artifacts.
