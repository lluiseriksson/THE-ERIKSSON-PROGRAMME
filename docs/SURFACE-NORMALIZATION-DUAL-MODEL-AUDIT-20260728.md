# Surface normalization dual-model audit

**Date:** 2026-07-28

**State:** adversarial design audit only; no K2, K4, S1/S2, gate, or
manuscript promotion.

## Verified consultations

Claude Fable 5 High was called through Fable Bridge with the explicitly
selected profile `masterythief`; the bridge reported authenticated account
`masterythief@gmail.com`, `verified_model: claude-fable-5`, and no error.

Claude Opus 5 Max was called through the local Claude CLI with the same
profile, no tools, `--model claude-opus-5`, and `--effort max`.  Its JSON
reported `is_error: false` and a `modelUsage` entry named exactly
`claude-opus-5`.

Neither answer is evidence.  Every accepted point below was rederived or
tested independently.

A later Fable-Bridge request for the companion-error propagation was
rejected by the bridge itself: although the selected profile and account
were correct, `modelUsage` named `claude-opus-4-8` and did not verify
`claude-fable-5`.  That response is not represented below as Fable evidence
and was not used to authorize a patch.

## Accepted and independently reproduced

Fable independently recovered

```text
H0/K0 = 1/(8c),
Y_full = 4 B_full/(delta KD_full^2),
corrected/historical = 8c.
```

The repository regression now tests two values of `c`, the required
K/H homogeneity, and the exact symbolic endpoint closed form.

Opus suggested changing coordinates before interval evaluation.  The useful
part has the following exact, independently derived form.  With

```text
dP_delta = K D dx / KD,
A = F/D,
R = (H/K) D,
```

one has

```text
B/KD^2 = Cov_P(A,R).
```

Since `R(0)=1/(4c)` is spatially constant, define

```text
G = (R-1/(4c))/delta.
```

Then the removable-singularity identity is

```text
Y = 4 Cov_P(A,G).
```

The symbolic moment identity and finiteness of the pointwise `G` series at
`delta=0` are executable in
`tests/test_surface_k2_kd_covariance.py`.  A numerical conditioning probe is
design-only until companion, exterior, and uniform-delta charges are added.
With exact separated Gaussian KD cell masses, its enclosure radius contracts
from about `897` at grid 12 to `5.289` at grid 24.  The earlier covariance
coordinate had radius about `211` at grid 24.  This is a material
conditioning improvement, not a K2 bound; the grid-48 experiment is separately
pre-registered before execution.

## Rejected model claims

Fable warned that `B(0)=0` might fail on a truncated fixed square.  Direct
algebra refutes that warning: at `delta=0`, `H=(1/(8c))K` and `D=2`
pointwise, hence `HDF=(1/(4c))KF` and `HDD=(1/(4c))KD` after integration
over any common fixed domain.  The bilinear therefore cancels exactly.  A
regression test records the pointwise relations.

Opus multiplied the corrected fixed-square S2 fraction `1.781` by `8c` once
more.  That is wrong: `1.781` was already computed after the correction.
Opus also proposed redefining K4 as a `t`-uniformity statement, whereas the
registered K4 contract is the fixed-domain complement/cutoff obligation.
Neither suggestion is used.

## Current consequence

The dual audit strengthens the incident diagnosis and supplies a promising
conditioning coordinate, but does not restore a single withdrawn manifest.
K2 still requires corrected endpoint and regular-extension production plus
replay.  K4 and the analytic endpoint part of the weighted S1/S2 judges
remain separate open obligations.
