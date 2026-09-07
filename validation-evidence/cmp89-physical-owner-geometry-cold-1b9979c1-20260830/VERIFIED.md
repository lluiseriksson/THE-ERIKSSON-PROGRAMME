# CMP89 physical rectangle/owner geometry cold evidence

- Source checkpoint: `1b9979c1371c68b6aaa9722afaa1314c41adfa49`.
- Runner checkpoint: `f773c8cd67b3161ae4ddda393834a3ed5a5932e5`.
- Fresh Colab Pro+ CPU/high-RAM checkout; no project `.lake/build` restored.
- Lean: `4.29.0-rc6`; pinned Mathlib: `07642720480157414db592fa85b626dafb71355b`.
- Reflection-period focal: `8562/8562` jobs, exit zero, `1316.813` seconds.
- Reflection-period audit: exit zero, `6.118` seconds.
- Physical-owner-geometry focal: `8661/8661` jobs, exit zero, `394.266` seconds.
- Physical-owner-geometry audit: exit zero, `6.567` seconds.
- Six exact axiom readouts are contained in
  `{propext, Classical.choice, Quot.sound}`; no forbidden axiom token.
- Evidence JSON SHA-256:
  `8F30E9263C3CC82912B85809512EE6DC7F94E7524653A048513F0F97A6E67E6F`.
- Internal manifest SHA-256:
  `29E39E4EBCC004752C9BBAE0177C478C68B6A91B65EB791C192E1F8AD0B311FB`.
- Downloaded archive SHA-256:
  `6AB36EA5A11D6120544204B2E70A4D1680998872C6002B84E167D5B3B477AF08`.
- Local fail-closed verification emitted
  `CMP89_PHYSICAL_OWNER_GEOMETRY_EVIDENCE_OK`; all 15 manifest entries
  rehashed with zero mismatches.

This seal constructs only the reflection-period floor, physical rectangle
embedding and canonical CMP99 owner-metric bridge.  It does not construct the
CMP89 (2.42) representation certificate, produce a depth-uniform physical
`B0, delta0` pair, attain window 15, move `20/41`, or instantiate `TermSource`.
