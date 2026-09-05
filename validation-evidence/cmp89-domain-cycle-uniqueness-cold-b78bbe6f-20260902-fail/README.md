# CMP89 (2.46) domain/cycle/uniqueness cold gate — failed focal

Fresh Colab Pro+ CPU/high-RAM runner
`cmp89-eq246-domain-cycle-uniqueness-cold-v1` checked out exact source
`b78bbe6f8ae609f88c7396e58a6a4527945f427f`, verified the pinned Lean
toolchain and Mathlib commit, restored no project `.lake/build` graph, and
passed the textual hash/import gates for all six source blobs.

`BalabanCMP89Eq246FullSolutionDomain` compiled in `1099.528 s` and its exact
audit passed in `8.279 s`.  The stop-on-first-error queue then halted while
building `BalabanCMP89Eq246AliasCycleTransport` after `33.455 s`; neither its
audit nor `BalabanCMP89Eq246AliasPrecisionUniqueness` was checked.

The original browser cell transcript was lost when the Colab tab closed.
The canonical runner archive is preserved here and independently passes the
local evidence verifier with `STATUS=FAIL`.  After reconnecting to the same
retained runtime, the exact failed target was rerun once against the same
checkout.  The executed debug notebook preserved here records exit code `1`
after `11.606 s` and the first real errors: at source lines 72, 94 and 119,
Lean could not infer the factor argument `F` of
`cmp89Eq248AliasFactor_physicalShift_eq_cycle` through, respectively, the
opposite-momentum negation and the two endpoint exponentials.

The repair names those three existing factors explicitly.  It changes no
theorem statement, source identity, constant or hypothesis.  All six
PRE-VALIDATION notices remain until a later successful compiler and axiom
gate.

- evidence payload SHA-256:
  `4F49B1054E29FE03E8B3EABD572F90567E5B2E4598024BD6A787E0DE65BBFB8C`
- runner archive SHA-256:
  `208CAE8E85FF947308CDDBF3722AADFF73D25C0DB3C3672125596C37874DC254`
- executed debug notebook SHA-256:
  `E24369FFF299384B5BAE2DD911CFD6CE740409B12556D6A0FFE9EA1FC2F2E3B4`

This is failed evidence, not a seal.  Counters remain exactly `20/41`,
`TermSource = 0`, and window 15 remains compatible but unattained.
