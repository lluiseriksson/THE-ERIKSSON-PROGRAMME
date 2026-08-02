# ai.viXra submission record — critical-rescaling Fourier no-go v1.1

## Status

- Submitted: **2026-08-02**
- Version: **1.1 — closed; no v1.2 planned**
- Submission operation: **not restated in the owner closeout**
- Category: **not restated in the owner closeout**
- Public ai.viXra identifier: **not yet supplied in this record**

This record preserves only fields and artifact identities that were supplied
or independently reproduced. It does not infer a category, operation, or
public identifier from the subject matter.

## Title and author

**Fourier Transverse Modes Obstruct Volume-Uniform Critical Coercivity in a
Flat Lattice Gauge Block Form**

Lluis Eriksson

## Immutable artifact identities

| Artifact | Filename | SHA-256 |
|---|---|---|
| Submitted v1.1 PDF | `critical_rescaling_fourier_no_go_v1.1.pdf` | `B8E655D3F1253D0EA915BA54DF00A5C72F4CE5B5D229F74FE82EC152333EA726` |
| Formal source ZIP | `critical_rescaling_fourier_no_go_sources_v1.1.zip` | `AEF0AEAB6841FE4B26F6A5160305793646083EB72166BC5C751C8E2A5AA88132` |

The PDF is 8 pages and 303,938 bytes. The source ZIP is 14,511 bytes. Neither
artifact is to be regenerated as part of this documentation update.

## Formalization provenance

- Manifest: `papers/critical-rescaling-no-go-all-coarse/FORMALIZATION-MANIFEST-v1.1.txt`
- Main theorem: `YangMills/RG/PhysicalCriticalRescalingFourierNoGoAllScales.lean`
- Formal source checkpoint recorded by the manifest:
  `f21539ed0bb880a04078de369bf5cbf063f7b101`
- Spectral guardrail checkpoint reported by the owner:
  `574ac60246a54ff58efb080907e48bae71762026`
- Lean: `v4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`
- Focused theorem build: 8,184 jobs, successful
- Aggregate core build: 8,481 jobs, successful
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- No `sorry`, `admit`, or project axiom in the seven manifest-listed files

The cited checkpoints are provenance labels from the producing checkout. This
submission record does not claim that every checkpoint is already reachable
from a published remote ref.

## Exact claim boundary

For every `L >= 2`, every fixed positive `N'`, and `Nc >= 2`, the paper
constructs an explicit transverse Fourier witness in `ker Q_L` and the flat
divergence kernel. Its exact Rayleigh quotient is

`lambda_L = 4 sin^2(pi/L)`.

Consequently the best full-space coercivity constant satisfies
`c_L <= lambda_L`, and the corresponding Poincaré constant obeys
`C_P(L) >= 1/lambda_L >= L^2/(4 pi^2)`. The no-go result needs only this
explicit witness and inequality.

The paper does **not** claim that the witness minimizes the form over all of
`ker Q_L ∩ ker delta`.

## Spectral guardrail

The tempting equality between the restricted spectral bottom and `lambda_L`
is false in general. At `L = N' = 2`, the block profile

`(1,-1 | -1,1)`

lies in `ker Q_2 ∩ ker delta`, has squared norm `4`, energy `8`, and hence
Rayleigh quotient `2 < lambda_2 = 4`. The Fourier mode in the paper is
therefore an exact witness, not necessarily the minimizer of the complete
restricted sector.

Any continuation must use coarse-Bloch decomposition, impose the exact block
and divergence constraints, diagonalize the constrained finite family at each
coarse quasi-momentum, and only then minimize. The full guardrail is recorded
in `docs/FOURIER-NOGO-SPECTRAL-GUARDRAIL.md` in the producing checkout.

## Editorial closeout

- Absolute assessment reported by the owner: **4.75/10**
- Specialized formalization assessment: **9.15/10**
- Joint provisional assessment with Combes--Thomas v0.7: **5.08/10**
- Decision: keep v1.1 unchanged; no further editorial revision

These editorial assessments are not proof-state metrics and do not affect the
dashboard DAG or the recorded distance to the Clay problem.
