# Exact four-cycle fixed-penalty obstruction

This package preserves the finite counterexample in
`../mean-budget-order-20261101/interblock-shorted-energy.md` as ten Lean
theorems. It does not introduce another research question or a separate paper.

The successfully checked immutable Lean source is
`41f8492c619000b932778c67f3196fccee6a12d1`. `colab118.py` and the clean
`colab118.ipynb` pin that source, Lean 4.29.0-rc6 and the repository's Mathlib
revision. Execute only in a new own Colab Linux CPU/high-RAM runtime, prepared
while disconnected. The recipe releases that runtime after success or failure.

The recipe creates two fresh sparse clones, builds the focal module, runs the
ten-target axiom oracle, and validates the oracle in Python normal and optimized
modes in each clone. Three actual corrupted-oracle mutations must be rejected.
The two fresh module hashes and complete oracle outputs must agree. Upstream
Mathlib cache artifacts are used; this is not a rebuild of Mathlib.

The cycle has weights (1,6,4,1), mean weight 3, and two blocks {0,1}, {2,3}.
For the counting Euclidean norm and normalized block means, kernel coercivity
holds with c=19/5. The explicit field (19,-9,-5,-5)/14 has energy 52/7,
norm squared 123/49 and observed norm squared 25/49. Its full fixed-penalty
defect is -6/35. The Lean definitions use explicit sums of squares and actual
normalized means, avoiding any reliance on a default norm on function spaces.

This refutes the implication from coercivity on the observation kernel to
coercivity with the *same fixed penalty*. It does not refute existence of an
arbitrary larger penalty, every allowed rectangular partition, or the open
critical-moment rectangular-mean target. It proves no physical-lattice
embedding, interacting spectral gap, or continuum result. PR29 remains
20/41 and TermSource=0.

## Model assessments and review context

Prepared and operated by the same Codex agent. The served backend model and
reasoning setting were not exposed in the session. Compiler/oracle validation
is formal checking, not an independent model review or human peer review.
No numerical assessment is assigned here. Historical manuscript or analytic
note grades do not apply to this source or this package. No originality claim,
AIRR acceptance or publication is made by preparation of these artifacts.

Actual execution status, complete logs and artifact hashes must be read from
the preserved run report and archive; an unexecuted notebook alone is no
evidence of successful compilation.

## Actual execution and preserved failures

Own Colab118 ran from 2026-11-03 22:58:57.002727 UTC to
23:03:41.573111 UTC. Both fresh focal builds and both actual oracles exited
zero. Each of the four normal/optimized validator runs accepted all ten
readouts and rejected all three real corruptions. All readouts use only
`propext`, `Classical.choice`, and `Quot.sound`. Both fresh `.olean` hashes
equal `5ac803d0c9ae015c22b5921cc65599ceda668577761dc1ad5ac740532a8760d4`;
both complete oracle-log hashes equal
`d1b2c71a4236342b67f9750fb0af9607ff3909516b6b77a16e67c836e8077643`.

The full 29,499-byte Colab118 archive is `evidence/colab118-full.zip`, SHA256
`a6a8b79ca85d7f28a539dcc74c7a66f8a7e2a44ca41f8d75d5f459b47a78002b`.
Its 69 manifest entries, report, actual decimal exit sentinels and complete
validator outputs were recovered and checked. Host-side work checked hashes,
JSON and archive consistency; Lean and all mathematical execution stayed in
Colab. The runtime released itself; the resource UI subsequently showed zero
active sessions. Precise allocation/total connected duration was not exposed;
the timestamps above measure the script interval only.

Earlier attempts are retained in full, not replaced by the successful report:

| Run | Immutable source | Actual result |
| --- | --- | --- |
| 116 | `86ed176be451415f7e43506b62e59d5040c099b7` | build exit 1: real noncomputability and finite-vector simplification |
| 117 | `e6d137d2bf21d7fdd2e2f5a25a31b01c263fdaa2` | build exit 1: finite-index comparisons and missing unnamed-section end |
| 118 | `41f8492c619000b932778c67f3196fccee6a12d1` | paired build/oracle pass |

The two failed archives have SHA256
`f56eb3e2260c120381f6cc5f7acf301800ea96f241040452375a93c70980b366`
and `e78725896c3f8a62aa6f9817d1a00898187c870b182b9900f41c129019a1441d`.
All failures concern representation/elaboration; the theorem statements and
numerical witness were not weakened. This formal preservation does not reset
the stopped research-route counters or claim a new global endpoint advance.
