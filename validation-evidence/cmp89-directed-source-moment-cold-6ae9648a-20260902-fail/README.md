# CMP89 directed source-moment cold failure

- runner revision: `cmp89-eq246-directed-source-moment-cold-v1`
- runner commit: `d90d208a3889a0dde5576b87fa9aace6cc2363b0`
- runner Git-blob SHA-256: `a4ee1f32fb4c1b680ee9d5493ebd063aa3bcef70d2261078b13375cb2a3b1df6`
- notebook commit: `0b920c3ebe3398b7c1a8d1a2cdbc2547580ee5cc`
- exact source: `6ae9648a61be6f5be62b351b2c0ab2da1c45cfe9`
- result: `FINAL_STATUS=FAIL`
- first failing stage: `directed_source_moment_focal`
- focal exit: `1` after `1500.562 s`
- archive SHA-256: `974151A9C568DB8BFFE335AD86C89174DE875AB8AF784B792D6D653F0AD543B3`
- runner payload SHA-256: `30403A35C91A199A684252EA2CDB9DC6DBF3CDC2BA68FFBB59F7FF50D13F082B`
- archived `evidence.json` SHA-256: `10AC2673C529C57E248C22DB3D3881A9EE8FC18F4EF11496B79B1FFE1D06B8AD`

The fail-closed verifier
`tmp/audit_cmp89_eq246_directed_source_moment_cold_evidence.py` accepts the
exact runner/source/toolchain/Mathlib fields, both Git-blob hashes and the
single-stage stop-on-first-error queue.

The exact Lean failure is
`BalabanCMP89Eq246DirectedSourceMoment.lean:101:10`: tactic `rfl` did not
normalize the associativity difference between `A * (g * C)` and
`(A * exp(...) ) * C`. All dependencies reached `8508/8509`; the audit did
not run. The repair changes only that normalization to
`simpa only [g, mul_assoc]`. PRE-VALIDATION remains in force and this archive
is not compiler evidence for the repair.

The Colab runtime was disconnected and deleted after the archive was
exported and verified. Counters remain `20/41`, window 15 remains compatible
but unattained, and `TermSource = 0` remains exact.
