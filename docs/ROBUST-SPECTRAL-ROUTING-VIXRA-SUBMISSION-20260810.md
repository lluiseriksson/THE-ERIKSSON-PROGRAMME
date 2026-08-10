# Robust spectral-routing paper — viXra submission record

Date recorded: **2026-08-10**

Owner-reported operation: **new paper sent to viXra**

Moderation/publication outcome and viXra identifier: **not recorded here**

## Paper identity

Full displayed and submission title:

*Every Spectral Switch Costs Memory: Sharp Robust Wigner–Smith Speed Limits
for Passive Quantum Networks*

- Author: **Lluis Eriksson**
- Category entered: **Quantum Physics**
- Language: **English**
- Immutable release:
  [`v1.3-robust-spectral-routing`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/tag/v1.3-robust-spectral-routing)
- Release/source commit:
  [`e4d8989f59a2a6f881db0e9f91299150b5fbaacc`](https://github.com/lluiseriksson/finite-sample-spectral-certificates/commit/e4d8989f59a2a6f881db0e9f91299150b5fbaacc)
- Research PR:
  [finite-sample-spectral-certificates #5](https://github.com/lluiseriksson/finite-sample-spectral-certificates/pull/5)

The embedded PDF metadata uses the shorter title *Every Spectral Switch Costs
Memory*. The first page displays the full title above; this record keeps the
two identities distinct.

## Exact submitted PDF and release assets

- [Release PDF](https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/download/v1.3-robust-spectral-routing/every_spectral_switch_costs_memory.pdf)
- Pages: **11**
- Bytes: **339,660**
- SHA-256: `795E03238F152B48241E49B3DB924497DAE16D9E13ABDA725E43ED3B60C1F4FF`
- GitHub release publication time: **2026-08-10 10:52:24 UTC**

Additional frozen release assets:

- `certificate.json`: 11,561 bytes, SHA-256
  `F23444637EF7E3A059ACE12060E8481692B700611687DEF4277CDDAFD45399CA`;
- `ROUTING_SPEED_LIMIT_ARTIFACT.json`: 1,734 bytes, SHA-256
  `65D5DB54E183F82CB7FB6198E16646C8E24504B8DFC376B2F064224E727193FF`.

The GitHub release API and an independent download agree on the PDF byte
count and digest. The page count, displayed title and author were recomputed
from the downloaded PDF. PR #5 is open as a draft at the release commit; its
visible numerical and kernel-checked CI runs were all green when this record
was prepared.

## Exact form metadata

Comments:

> 11 pages, 1 figure. Reproducible certificate, source and verifier:
> https://github.com/lluiseriksson/finite-sample-spectral-certificates/releases/tag/v1.3-robust-spectral-routing

Keywords:

> Wigner–Smith time delay; McMillan degree; passive quantum networks;
> approximate spectral routing; Grassmannian; rational inner functions;
> robust interpolation.

Abstract:

> Exact interpolation can force the internal degree of a passive network, but
> laboratory calibrations are approximate. We prove a sharp frequency-domain
> speed limit requiring neither exact zeros nor analytic continuation away
> from the measured frequency axis. Let S(exp(i theta)) be an absolutely
> continuous unitary scattering path with positive Wigner–Smith generator
> Q(theta) = -i S(exp(i theta))^* partial_theta S(exp(i theta)) >= 0. If a
> fixed k-dimensional input subspace is routed approximately between
> complementary output sectors with amplitude leakages epsilon_p, epsilon_s,
> define alpha = [pi/2 - arcsin epsilon_p - arcsin epsilon_s]_+. Every
> transition then requires Wigner–Smith trace action at least 2 k alpha and
> largest-proper-delay action at least 2 alpha. Costs add over disjoint
> frequency arcs. For a rational inner network of McMillan degree n, M
> alternating pass/stop pairs imply n >= 2 M k alpha / pi, recovering n >= M k
> at zero error. An explicit 2k-port interferometric family attains the bounds
> for every admissible error pair. A tomography-error corollary converts finite
> scattering measurements directly into certified degree and delay lower
> bounds. Reproducible certificates audit equality cases, positive-block
> inequalities and random Blaschke–Potapov products.

## Mathematical scope recorded

The paper realizes the robust boundary-measurement direction identified after
the exact-calibration paper. Its central parameter and bounds are

```text
alpha = [pi/2 - arcsin(epsilon_p) - arcsin(epsilon_s)]_+

integral_I tr Q(theta) d theta          >= 2 k alpha
integral_I lambda_max(Q(theta)) d theta >= 2 alpha
n >= 2 M k alpha / pi.
```

The contribution claimed is the leakage-to-angular-separation-to-trace-action
to-McMillan chain, together with additivity on disjoint arcs, a tomography rule
and multichannel sharpness. It does not rely on exact boundary zeros or on
analytic continuation away from the measured frequency axis.

## Known bibliographic limitation of the submitted object

The pre-submission assessment recommended an explicit comparison with known
operator-norm subspace speed limits, especially Albeverio–Motovilov, and with
modern operator-flow speed limits by Hörnedal and collaborators and by Carabba
and collaborators. Text extraction from the immutable submitted PDF contains
none of the author names `Albeverio`, `Motovilov`, `Hörnedal`/`Hornedal`, or
`Carabba`.

Therefore this record does **not** claim that the recommended bibliographic
correction was incorporated. The defensible priority boundary is narrower:
operator-norm subspace speed-limit components have antecedents; the claimed
contribution is their passive-network leakage-to-trace-action-to-McMillan
composition, tomography rule, additivity and sharp multichannel realization.
Any replacement should update the complete metadata record as well as the PDF.

## Lifecycle

The public GitHub release is immutable evidence, not evidence of viXra
acceptance. Until a public identifier or moderation result is supplied, the
submission remains recorded as **submitted / pending outcome**. The paper is
maintained in the separate `finite-sample-spectral-certificates` repository
and does not change the canonical Yang–Mills proof-state checkpoint here.
