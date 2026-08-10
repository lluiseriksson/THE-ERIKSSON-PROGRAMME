# Exact Finsler speed-limits paper — viXra submission record

Date recorded: **2026-08-10**

Owner-reported operation: **paper sent to viXra**

Moderation/publication outcome and public viXra identifier: **not recorded
here**

## Paper identity

Full displayed title:

*Proper-Delay Spectra Majorize Subspace Rotation: Exact Finsler Resource Laws
for Passive Networks*

- Author: **Lluis Eriksson**
- Immutable release:
  [`v1.5-exact-finsler-speed-limits`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/tag/v1.5-exact-finsler-speed-limits)
- Release/source commit:
  [`53a845e0a72cce633154887de7fffb41913527cd`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/commit/53a845e0a72cce633154887de7fffb41913527cd)
- Research PR:
  [finite-sample-spectral-certificates #6](https://github.com/lluiseriksson/finite-sample-spectral-certificates/pull/6)
- Immutable CI run:
  [`31389325905`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/actions/runs/31389325905)

The PDF metadata title and author agree with the displayed first page.

## Exact submitted PDF and release assets

- [Release PDF](https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/download/v1.5-exact-finsler-speed-limits/proper_delay_spectra_majorize_subspace_rotation.pdf)
- Pages: **11**
- Bytes: **348,460**
- SHA-256: `BE4BB95E0E7B833A8D2201DAB60846A43DF1D06F02DD292644FF9FCC80DE3D42`
- GitHub release publication time: **2026-08-10 12:42:59 UTC**

Additional frozen release assets:

- `certificate.json`: 7,447 bytes, SHA-256
  `0D07EB630A9DFD5A8F421A001A409ECD60F5F7C56173BC95A61A29966183287F`;
- `KY_FAN_SPEED_LIMIT_ARTIFACT.json`: 1,830 bytes, SHA-256
  `FDED2139D9C44FAE85AD81F575F950BE40C9AACE15546783C33E9B266B72D16C`.

The local and release PDFs are byte-identical. Their sizes and SHA-256 digest
agree with the release API. The 11 pages were rendered and inspected: no
clipping, overlap, broken glyph, table failure or figure-composition defect was
observed. PR #6 is open as a draft at the release commit and all six visible
numerical/kernel-checked CI runs were green when this record was prepared.

## Mathematical scope recorded

For canonical-angle vector `beta` and every symmetric gauge `Phi`, the paper
proves the exact variational law

```text
inf A_Phi = 2 Phi(beta).
```

One constant positive coupled-mode path simultaneously attains the optimum for
all symmetric gauges. The preceding Ky Fan hierarchy weakly majorizes twice
the canonical-angle vector by the integrated spectral-spread vector; for
positive Wigner–Smith flows this becomes a hierarchy for leading proper-delay
action.

The paper also records:

- a strict intermediate-prefix separation of **20%** that is invisible to the
  maximum-angle and trace endpoints;
- an exact slack decomposition and quantitative near-rigidity bounds;
- heterogeneous robust routing and finite-error tomography;
- additivity and the rational McMillan-degree consequence;
- a deterministic certificate covering sharp equality families, matrix
  inequalities, noncommuting piecewise-constant paths and noisy tomography.

The paper's claim is a vector/gauge resource law, not merely another maximum-
delay or trace-delay bound. Its references explicitly include
Albeverio–Motovilov and Hörnedal and collaborators, addressing the named
operator-speed-limit antecedents that were absent from the preceding v1.3
spectral-routing submission.

No external editorial score or novelty judgment is inferred from the release
or CI. The analytic proofs remain the evidence for the mathematical claims;
the numerical artifacts are adversarial implementation audits.

## Lifecycle

The GitHub release is an immutable public evidence object, not proof of viXra
acceptance. Until a public identifier or moderation result is supplied, this
submission remains **submitted / pending outcome**. It is maintained in the
separate `finite-sample-spectral-certificates` repository and does not alter
the canonical Yang–Mills proof-state checkpoint here.
