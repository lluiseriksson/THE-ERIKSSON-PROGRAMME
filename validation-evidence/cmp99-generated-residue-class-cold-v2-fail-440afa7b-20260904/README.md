# CMP99 generated residue-class cold v2 — instrumentation failure

- Source: `440afa7b0883cc77a30f2457c879b025dcde32f1`
- Runner checkpoint: `44fe2d84c3165348cad5076a095864d11723dbcd`
- Runner SHA-256: `083ac8c1df7f1a074958f1419285e2388b4dec07304d73eee00e6500651ad30f`
- Evidence archive SHA-256: `dcb77b86489709ae7ee494f5ea5531968c3b00a04e46990173e98edb4d190cf6`
- Focal: exit `0`, `2398.055` seconds
- Audit: exit `0`, `22.948` seconds
- Manifest status: `FAIL`

The compiler and audit both passed. The runner supplied only the terminal
theorem to the exact axiom parser, while the audit intentionally prints four
declarations. The parser therefore rejected the successful audit by block
count. A direct retained-runtime rerun confirmed all four declarations use
exactly `propext`, `Classical.choice`, and `Quot.sound`.

This archive is retained as `BLOCKED-INSTRUMENTATION`; it is not cold-seal
evidence and does not retire PRE-VALIDATION.
