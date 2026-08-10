# Lossless calibration memory paper — viXra submission record

Date recorded: **2026-08-10**

Owner-reported operation: **paper sent to viXra**

Moderation/publication outcome and viXra identifier: **not recorded here**

## Paper identity

Full displayed and submission title:

*Lossless Calibration Is Stored Memory: A Topological McMillan-Degree and
Wigner–Smith Law for Passive Quantum Networks*

- Author: **Lluis Eriksson**
- Immutable release:
  [`v1.2-topological-calibration-memory`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/tag/v1.2-topological-calibration-memory)
- Release/source commit:
  [`a52d6e74dba697477acf9204077a1b67ffe56dfc`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/commit/a52d6e74dba697477acf9204077a1b67ffe56dfc)
- Research branch:
  [`research/topological-calibration-memory`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/tree/research/topological-calibration-memory/paper_calibration_memory)
- Research PR:
  [finite-sample-spectral-certificates #4](https://github.com/lluiseriksson/finite-sample-spectral-certificates/pull/4)

The PDF metadata uses the shorter title *Lossless Calibration Is Stored
Memory*. The first page displays the full title above; this record preserves
the distinction instead of treating the embedded metadata title as the form
title.

## Exact submitted PDF

- [Release PDF](https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/download/v1.2-topological-calibration-memory/lossless_calibration_memory.pdf)
- Pages: **13**
- Bytes: **388,593**
- SHA-256: `89ACD5362D43022C78FF694ED414F9134E995472CC2DB1E0974A0021589D8C61`
- GitHub release publication time: **2026-08-10 09:18:09 UTC**

The release API reports the same byte count and digest. The PDF was also
downloaded independently and its byte count, SHA-256, page count, displayed
title and author were recomputed.

The release additionally contains the 5,769-byte numerical certificate
`certificate.json`, SHA-256
`0F1F5F033970D27BEF4DDFC56AECAC8D8E9F49386E9FBE830DFCFED6CD1AE1B7`.

## Mathematical scope recorded

For a causal rational-inner passive network with scattering matrix `S`, signal
block `G`, McMillan degree `n`, and distinct regular boundary calibration
frequencies, the paper relates the total dimension of exactly lossless signal
directions to stored internal degree and integrated Wigner–Smith delay:

```text
K = sum_j dim ker(I - G(zeta_j)^* G(zeta_j))
  <= deg_McM S
   = (1 / 2 pi) integral tr Q(theta) d theta.
```

The stated result is architecture-independent within the finite-dimensional
rational-inner setting. The paper includes a sharp construction, a Rouché
stability argument, and explains why clustered approximately lossless samples
without additional analytic control do not by themselves force a comparable
degree lower bound. The reported explicit family reaches `S=19`, calibration
load `K=57`, and degree `63`; the numerical package also includes certified
passive perturbations on 15 contours and tests of 128 random Potapov products.

All visible CI runs associated with PR #4 and the release commit were green
when this record was prepared, including the numerical and kernel-checked
jobs. This statement records CI status; it is not an independent mathematical
peer review.

## Priority and follow-up boundary

The reported `6.07/10` and first-place ranking are **internal provisional
evaluation**, not external editorial judgment. Classical literature already
covers substantial parts of minimal-degree tangential interpolation and
boundary interpolation by lossless or Blaschke functions. Consequently, the
paper's priority claim must be limited to the exact chain it establishes;
terminal bibliographic review remains appropriate before claiming broader
novelty.

A proposed robust real-axis law for alternating approximate pass and stop
calibrations,

```text
n >= (M k / pi) (sqrt(1 - epsilon_s^2) - epsilon_p),
```

is recorded as **future work**, not as a theorem of this release. Developing or
sharpening that law would be a new paper rather than an extension silently
attributed to the submitted PDF.

**Subsequent status.** Later on 2026-08-10 that direction was realized as the
separate paper *Every Spectral Switch Costs Memory*, with its own immutable
release and [submission record](ROBUST-SPECTRAL-ROUTING-VIXRA-SUBMISSION-20260810.md).
This does not retroactively add the robust theorem to the exact-calibration
PDF; it preserves the intended separation between the two papers.

## Lifecycle

The GitHub release is an immutable public evidence object. Its publication
does not prove viXra acceptance. Until a public identifier or moderation result
is supplied, this submission remains recorded as **submitted / pending
outcome**. It belongs to the separate
`finite-sample-spectral-certificates` repository and does not alter the
canonical Yang–Mills proof-state checkpoint in this repository.
