# Draft: cold seal for full Eq. (2.46) endpoint domains

This file is a staging note only.  It is not compiler evidence and is not
part of the selective seal until the fresh Colab gate emits `FINAL_STATUS=PASS`
and its archive is preserved and independently checked.

Exact objects under test:

- source checkpoint: `e4f2bbc33599da7b0f7ff91deeb5307719616a25`
- cold runner checkpoint: `386c3c7e15702b56f82e29b227d9d3601d1feb89`
- cold runner SHA-256:
  `81f5bf48421204246bce75a23fa774ce9f28f39dc8f383639c6f013ee4043267`
- focal blob SHA-256:
  `5a5886676d522e5d47e261415db745e63cb8a831e5b4fd56482e31826c65d977`
- audit blob SHA-256:
  `5ecef456c76d34d107a9e81a14ecfa4c2472f95f51f1d251457d73464ec11e25`

On PASS, retire exactly the two PRE-VALIDATION notices in:

- `YangMills/RG/BalabanCMP99SourceFlatFullPointSourceSolutionDomain.lean`
- `YangMills/RG/BalabanCMP99SourceFlatFullPointSourceSolutionDomainAudit.lean`

and import only the audit in `YangMillsCore.lean`.  Record focal/audit times,
job count, exact axiom blocks, evidence payload hash and archive hash from the
completed gate.  Preserve the archive under `validation-evidence/` before
disconnecting the runtime.

This is an endpoint-domain producer, not an identification between centered
and physical representatives.  It does not prove the mixed-coordinate
telescope, CMP89 (2.42), uniform `B0`/`delta0`, window-15 attainment, a
terminal field or a `TermSource`.  Counters remain exactly `20/41`, window 15
remains compatible but unattained, and `TermSource = 0` remains exact.
