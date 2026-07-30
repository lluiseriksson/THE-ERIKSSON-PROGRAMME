# Publication register

This is the repository's live crosswalk between public preprints and the exact
artifacts committed here.  It records publication metadata; it does not widen
the theorem statements of any paper.

**Last public check:** 2026-07-30 against
[`ai.viXra.org/author/lluis_eriksson`](https://ai.vixra.org/author/lluis_eriksson).
The newest public entry visible in that check is author-list item `[93]`,
`ai.viXra.org:2607.0078`.

## Latest public O-lane sequence

| Author list | Public ID | Archive timestamp | Repository artifact | Paper commit | Lean anchor | Binary audit |
|---:|---|---|---|---|---|---|
| `[93]` | [`2607.0078`](https://ai.vixra.org/abs/2607.0078) | 2026-07-28 13:19:32 | [`os_chain_z2.pdf`](../papers/os-chain-z2/os_chain_z2.pdf) | `0df60332` | `bd2c1839` | exact |
| `[92]` | [`2607.0076`](https://ai.vixra.org/abs/2607.0076) | 2026-07-28 17:10:48 | [`os_quotient.pdf`](../papers/os-quotient/os_quotient.pdf) | `fddecd37` | `673d1df1` | exact |
| `[91]` | [`2607.0075`](https://ai.vixra.org/abs/2607.0075) | 2026-07-28 19:17:42 | [`spatial_extent.pdf`](../papers/spatial-extent/spatial_extent.pdf) | `959076f2` | `d8187d7f` | exact |
| `[90]` | [`2607.0073`](https://ai.vixra.org/abs/2607.0073) | 2026-07-27 21:33:38 | [`reflection_positivity.pdf`](../papers/reflection-positivity/reflection_positivity.pdf) | `b93d82b7` | `bbadf68c` | exact |
| `[89]` | [`2607.0070`](https://ai.vixra.org/abs/2607.0070) | 2026-07-27 16:38:14 | [`o_bridge.pdf`](../papers/o-bridge/o_bridge.pdf) | `d97ba949` | `ad9c93d7` | exact |

“Exact” means that the SHA-256 of the public `v1` PDF downloaded on
2026-07-29 equals the SHA-256 of the repository PDF:

| Public ID | Title | PDF bytes | SHA-256 |
|---|---|---:|---|
| `2607.0078` | *From the Gibbs Weight to the Spectral Gap: A Complete Machine-Checked Osterwalder-Seiler Chain for the Z_2 Lattice Gauge Chain* | 117,363 | `8b52725dfa42a40b119b4dc4a34dd4b5b326fc11bca2cd008dfa384f3675f3c4` |
| `2607.0076` | *The Quotient That Is Not the Identity: A Machine-Checked Degenerate Reflection Pairing and Its Gelfand-Naimark-Segal Quotient* | 92,307 | `ee99c158af94fced1eecfc0aa0a26121aadea576e7dd0ba33d7e2538c309dd1f` |
| `2607.0075` | *Where the Elementary Reconstruction Stops: Spatial Coupling Breaks the Uniform Vacuum, Machine-Checked* | 86,493 | `c519a6a1592ee25b36df6e1710c7d629d2305ee3885f0c7993b60a2b6639bef4` |
| `2607.0073` | *A Machine-Checked Reflection-Positivity Framework for Z_N Lattice Gauge Theory, with the Z_2 Wilson Instance* | 91,268 | `95c85d5b89f10b07e83fc699af0e03d45b35aec75851dda0d263b3c788e8f47c` |
| `2607.0070` | *Clustering and the Transfer-Operator Gap: A Machine-Checked Dense-Family Criterion* | 112,653 | `56dcba9f6c88452570c427d337fa4e00a0ff9bfeb9087faa28826094d1f72ad5` |

The public and repository PDFs are therefore not merely title-matched: they
are byte-identical.

## Submitted or frozen artifacts without a public ID

| State | Artifact | Exact repository identity |
|---|---|---|
| Submitted to arXiv on 2026-07-30, owner report; public ID pending | *A Machine-Checked Thermodynamic Limit for Local Lattice Gauge Gibbs States* | repository checkpoint `d6282a83`, formal source checkpoint `0be45284`, PDF SHA-256 `0a494cd745da4760428ad4e915075469c95eab7e638856b5e49925ec662a0919`; see the [submission record](SUBMISSION-LOCAL-GIBBS-THERMODYNAMIC-LIMIT-20260730.md) |
| Submitted on 2026-07-30, owner report; public ID pending | *The Modulus: a Machine-Checked Operator Bound on the Fluctuation Sector of the Coupled Z_2 Slice* | paper `21199f40`, Lean `9704b3f3`, PDF SHA-256 `200cfe770180f86aa725683d20424772e009ccc980c991faa7f03f99b42287b8`; see the [submission record](O-LANE-SUBMISSION-SPATIAL-SPECTRAL-20260730.md) |
| Submitted on 2026-07-29, owner report; public ID pending | *The Measure the Spectral Results Were About: a Machine-Checked Transfer Bridge for the Spatial Z_2 Slice* | submitted v1.1: paper `dc2935eb`, Lean `c4fa6a9e`, PDF SHA-256 `92c8235c54c8c6cafa7325d1a126f8b962ea486ac9e95d2e0872ec25969ce243`; current repository erratum v1.2: paper `b0b4a32c`, PDF SHA-256 `0a0acc85773ff6557ca65b5a49027c29aeee99cd45e7861c474bd0bbe876ca18`; see the [submission record](O-LANE-SUBMISSION-SPATIAL-GIBBS-20260729.md) |
| Submitted on 2026-07-29, owner report; public ID pending | *Strict but Not Uniform: a Machine-Checked Spectral Gap at Every Finite Extent of the Coupled Slice* | paper `b03766bd`, Lean `ac897963`, PDF SHA-256 `e8063013965ea1699718d08f2bce1646e73f0dd2b970a518bb9e6339c68d78a0`; see the [submission record](O-LANE-SUBMISSION-PERRON-GAP-20260729.md) |
| Submitted on 2026-07-29, owner report; public ID pending | *Blind to the Coupling: a Second Machine-Checked Obstruction at Spatial Extent* | paper `3d313d92`, Lean `a70426f4`, PDF SHA-256 `42617528c0df0ad3e813ee77c11722c53e5ea1b4b97dc93f22d9ece45d29e4cb`; see the [submission record](O-LANE-SUBMISSION-SPATIAL-BIRKHOFF-20260729.md) |
| Frozen v1.1; submission not reported | *A Machine-Checked Perron Theorem for Strictly Positive Kernels, and the Coupled-Slice Vacuum at Every Spatial Extent* | paper `316648e2`, Lean `08a90502`, PDF SHA-256 `6349c8e555f10fde30e0457f54c841da9d05e252cf34e65f6a8064d463318e74` |

No identifier is inferred from ordering, submission time, or a nearby archive
number.  A pending row moves into the public table only after it appears on the
relevant public archive and its public PDF has been compared with the
repository artifact.

The thermodynamic-limit paper is not part of the numbered O-lane sequence.
It belongs to the independent uniform-KP lattice campaign recorded in
[`docs/THERMODYNAMIC-LIMIT-KP-PLAN.md`](THERMODYNAMIC-LIMIT-KP-PLAN.md).

## Claim boundary

The O-lane sequence verifies finite or exactly specified reconstruction
interfaces: the dense-family criterion, finite abelian reflection positivity,
the smallest complete `Z_2` chain, a genuinely degenerate quotient, the
spatial-extent obstruction, projective-metric blindness, and a Perron vacuum
for strictly positive finite kernels.  Paper 8 adds strict separation of every
non-Perron eigenvalue at each fixed finite extent.  Paper 9 supplies the
finite Gibbs measure-to-transfer bridge: unnormalised two-point sums become
matrix elements, normalised expectations become ratios with positive
denominator, and connected decay follows under an explicit contraction
hypothesis.  Paper 10 discharges that fixed-extent hypothesis by constructing
the sharp non-Perron modulus and its relative rate, and proves the normalised
two-point bound at fixed extent.  The rate remains extent-dependent.  The
sequence provides no volume-uniform interacting spectral gap, four-dimensional
continuum limit, or Clay Yang--Mills mass gap.

The local Gibbs thermodynamic-limit paper proves whole-sequence convergence
and a positive normalized real local state in an explicit strong-coupling KP
regime, with full integer-translation invariance, equality with one centered
free-boundary exhaustion, and passage of its stated two-plaquette bound.  It
does not claim arbitrary boundary conditions, a `C*`-algebraic state,
Osterwalder--Schrader reconstruction, a continuum limit, or the Clay mass gap.
