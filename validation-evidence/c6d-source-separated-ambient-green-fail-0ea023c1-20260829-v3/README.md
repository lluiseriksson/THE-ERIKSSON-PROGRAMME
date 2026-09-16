# C6d source-separated ambient Green cold FAIL (v3)

This directory preserves a single cold Colab execution.  It is failure
evidence, not a seal.

- source SHA: `0ea023c1a3589365dcc41a89514d1bff26c01080`
- runner revision: `c6d-source-separated-ambient-green-v3`
- Mathlib SHA: `07642720480157414db592fa85b626dafb71355b`
- toolchain asset SHA-256:
  `bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e`
- evidence JSON canonical SHA-256:
  `84D37468EB296018A52D3A63C0208C8D2007B02D657436356F4AF8DF00450687`
- evidence archive SHA-256:
  `B8F21A6ADFF0944B542F35933D7D87BCEE3D510AA2A9281CF52AA3521EEAECEE`
- executed notebook SHA-256:
  `3ECB2174343D524741AAEB8AA66E07BCFD87A4A1672A6BFD4DCD2608F987CD0B`

The downloaded archive hash matches the runner transcript.  All 19 archived
stage outputs were extracted, newline-normalized exactly as the terminal
verifier does, and checked against their `evidence.json` SHA-256 records.

## Passing prefix

- positive-depth Green focal: exit `0`, `8757` jobs, `2757.210` seconds;
- positive-depth audit: exit `0`, 15 allowed axiom readouts, `59.532` seconds;
- depth-zero Green focal: exit `0`, `8552` jobs, `55.076` seconds;
- depth-zero audit: exit `0`, 10 allowed axiom readouts, `47.327` seconds.

This prefix does not seal either Green module because the queue contract also
required the cold `YangMillsCore` root.

## First real failure

The root stage exited `1` after `9061.410` seconds while building
`BalabanCMP99Eq360C6dCanonicalAmbientCompletion.lean`:

- lines 122 and 124: unknown identifiers `A`, `hc`, and `hA`;
- subsequent deterministic `whnf`/`isDefEq` timeouts are downstream noise.

The source object predates the already published private-`NeZero`/scope
repairs.  No PRE-VALIDATION notice is retired, no hard counter moves, and no
focal-only PASS is promoted to a compiler seal from this run.
