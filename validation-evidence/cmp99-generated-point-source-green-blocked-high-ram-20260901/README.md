# CMP99 generated point-source Green — blocked high-RAM preflight

This archive records an instrumentation-only failure before checkout and before
any Lean, Lake, or axiom audit command ran.

- source checkpoint: `bd89724bbb926da4af507690773f32a84a657ccf`
- runner revision: `cmp99-generated-point-source-green-v1`
- observed runtime: CPU, 12.67 GiB RAM
- first error: `HIGH_RAM_REQUIRED`
- records: empty (`[]`)
- evidence archive SHA-256:
  `38FE1A44083193955793973C475972D80B88F77EC7C6F082C6335FA4C85E604A`
- opened/closed: 2026-09-01 12:33:52 UTC (preflight only)

Classification: `BLOCKED-HIGH-RAM`.  The six PRE-VALIDATION Lean modules were
not compiler-checked by this attempt.  It does not alter `20/41`, does not
instantiate `TermSource`, and does not attain window 15.
