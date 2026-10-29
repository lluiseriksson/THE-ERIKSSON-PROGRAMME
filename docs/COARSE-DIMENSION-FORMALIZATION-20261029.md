# Coarse dimension obstruction: formal contract

This module addresses the rank-nullity step of
[the analytic flat coarse-rank note](FLAT-COARSE-RANK-OBSTRUCTION-20261029.md).
It does not yet formalize the concrete Fourier cube or its Hodge energy.

`YangMills/RG/CoarseMeasurementDimensionObstruction.lean` contains three results:

| Declaration | What it proves |
|---|---|
| `exists_unseen_of_finrank_lt_measurement_add_repair` | A subspace larger than the coarse codomain dimension plus the repair rank contains a nonzero vector killed by both maps. |
| `factorized_coercivity_false_of_dimension_budget` | A strict low-energy bound on that subspace refutes the proposed full-space inequality, even with a nonlinear coarse penalty vanishing at zero. |
| `factorized_coercivity_dimension_budget` | Conversely, a valid full-space bound must pay that dimension/rank budget. |

The rank of the repair is the actual `finrank` of its linear range, rather than
the dimension of the whole fine codomain. The proof constructs the map from the
test subspace into the product of the coarse codomain and the repair range.
Injectivity would contradict the finite dimensions. A nonzero vector in its
kernel then defeats the energy inequality. Positivity and symmetry of the fine
repair are unnecessary for this necessary condition; the intended positive
operator case is included.

The coarse penalty has no regularity, positivity or growth assumptions, only
`Phi 0 = 0`. The coarse measurement and fine repair remain linear. The energy
function itself is arbitrary; only its bound on the explicit test subspace is
used. The strict inequality `b < c` is essential to the contradiction.

## Remaining concrete obligations

To obtain the analytic lattice endpoint in Lean, one still needs to construct
the real Fourier cube, prove its exact real dimension without counting conjugate
pairs twice, and derive its energy bound from the actual lattice stencils. The
abstract theorem must not be described as having discharged these hypotheses.
In particular, the explicit bound `CP(L) >= L^2/(4*pi^2*d)` remains an analytic
result until that construction is formally supplied.

This is a classical finite-dimensional argument, with no independent literature
novelty or physical spectral-gap claim. It supplies no hRpoly producer, transfer
matrix, continuum construction, or change to PR29's 20/41 and TermSource=0.

## Reproduction boundary

The frozen target, two LF source hashes, pinned Lean/Mathlib versions and three
expected oracle reports were registered before execution. A successful target
build and focused oracle in Colab establish this abstract module at the exact
source SHA only. The original eleven-file paper reproduction remains a distinct
already-completed focal target and was not rerun here.

Two fresh Colab CPU/high-RAM clones verified the unchanged source commit
`b2313402cefb896c899ab4afb3c4d2aed75d95d4` with Lean `v4.29.0-rc6` and Mathlib
`07642720480157414db592fa85b626dafb71355b`. The first build passed without a
source repair. Both runs produced exactly three oracle reports, each with only
`propext`, `Classical.choice`, and `Quot.sound`. The source code contains no
admitted proof or project axiom.

| Deterministic artifact | Matching SHA-256 in both runs |
|---|---|
| Target `.olean` | `3b7ad9bfdc70bd9f9d2ecdf844e597d9d2d993a08e7667b0e55134e5a6f3cf93` |
| Raw `oracle.log` | `07627b9f289ee4abd713a37f6eef3671380f7c5b4344f259ecf42bbc983ed7dc` |
| `source-hashes.json` | `bab5e6239fe17a38d218cc08622e062a25d9dfb0d7bc77e7f30bb2b59a445bc6` |

The exact LF-normalized theorem source digest is
`6b7ef2ba8cde4fdc01754dfafd2d6c8989298960c0c3f2b7439e5351334f2dc9`;
the oracle source digest is
`8ece9c8c5d3540ef201a44ec76a866e32efb6b6ca1e19b40c6915f7301235d2e`.
Full packages, validations, comparison and frozen notebook are in
[`reproducibility/coarse-dimension-20261029`](../reproducibility/coarse-dimension-20261029/).
ZIP digests differ because timestamps, run durations and logs differ:
run010 is `8a51fab50ef03abfd32ef9d4091c25e9bdf2df4520077c6616182d842bdc74c0`,
run011 is `db2bb1d87ed5e6e88be66f8e18418fc297369ff61ed87e7ce92009d912973801`.
Each package's twelve manifest entries, two frozen source bodies, nine exit-zero
steps and three raw reports were checked.

Run010 executed 15:41:37-15:44:13 UTC, run011 15:46:59-15:49:28 UTC on
29 October 2026. Each emitted persistent evidence and released its own runtime;
the reconnect control was observed afterward. No GPU or Windows Lean/Lake was
used. Compute units and allocation overhead were not measured. These two runs
establish module reproduction, not independent scientific review or a terminal
audit of the whole repository. Later documentation/evidence commits preserve
the checked source commit as an unchanged ancestor.
