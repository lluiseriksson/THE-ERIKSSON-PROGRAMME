# Census discrepancies - 2026-07-31

This file records identity, version, availability, and provenance conflicts found
while freezing the public corpus. It does **not** infer publication from a local
PDF, a build log, a submission form, or a manifest.

## P0: public-current object unavailable

| Object | Public evidence | Conflict | Consequence |
|---|---|---|---|
| `2512.0081v2` | The abstract page designates v2 as current. | `https://ai.vixra.org/pdf/2512.0081v2.pdf` returned HTTP 404 during the frozen capture. Public v1 remains downloadable (SHA-256 `4d2b2443bda740859f18a78e17b00490263e5dbb5dce6ecfdd93ed253340840b`, 13 pages), but it is historical, not current. | `REPLACE-VERSION` or repository-side restoration is required on availability grounds; mathematical verdict remains `REVIEW-PENDING` until v2 is obtained or reconstructed and audited. |

## P1: source and version provenance

| Source/object | Discrepancy | Evidence and handling |
|---|---|---|
| All 103 abstract pages | `citation_online_date` disagrees with the first timestamp in `Submission history` in every record. | Use the exact submission-history/listing timestamps. The mismatch is retained in the JSON; meta dates are never promoted to evidence. |
| `2607.0091v1` and `2607.0031v1` | `pdffonts` reports non-embedded base fonts (Helvetica/Courier families). | Record as reproducibility/portability risk. This alone is not a mathematical replacement decision. |
| Desktop `Papers publicados.txt` | Exactly 70 entries (64 `replaced`, 6 `submitted`), frozen 2026-07-09; current public page has 103. | Historical snapshot SHA-256 `a1c0bda2a429910913483545cf79b3685151cea437413dc803e86dfb64a58feb`. It stops at `2607.0005` and cannot be the current census. |
| Initial local checkout `12bf6e24` | Contained no tracked PDF or TeX paper sources. | `origin/main` at audit start was `f65e969cc165185e96184c0a16f362079ef2bd9e`, with 28 PDFs and 27 TeX files. Audit work is based on the remote SHA; the divergent checkout was preserved on its own branch, not rebased or overwritten. |
| `README.md` area-law citation | The public paper is `2607.0005`; the repository still contains the placeholder `ai.viXra:XXXX.XXXX`. | Treat repository navigation as stale until the final synchronized-documentation commit. |
| C5 (`papers/c5-crossing`) | C6 cites C5 as `2607.0037`, while C5's release manifest still says its own ID is pending/not sent. | Public page controls: `2607.0037` exists with the C5 title. The manifest is stale and must not override publication evidence. |
| O-lane forms and `LEEME.txt` | One local note says only O-bridge/reflection-positivity were sent; a later form says four papers were sent; older forms still say `READY`. | Public records, versions, and PDFs control. Local forms are treated only as workflow history. |
| Spatial Gibbs | Form says v1.1/`READY`/commit `dc2935eb`; adjacent PDF is byte-identical to repo v1.2, and commit `b0b4a32c` records an erratum after submission. | Submission fields must be regenerated from the audited current source/PDF, never copied from this form. |
| Perron Gap | Individual local copy is v1.1 SHA prefix `1520d3ab`; repository and newer `ENVIAR-AHORA` carry v1.2 SHA prefix `e8063013`. | The individual copy is stale. Public version comparison is required before any owner action. |
| Poincare paper | `origin/main` contains v1.2; a distinct v1.3 exists only on `origin/poincare-wall-unified-v1.3`. | `LISTO-LOCAL` cannot be assigned until the intended branch, public version, and claim delta are reconciled. |
| Surface papers | Partial `papers/surface-theorem` and later `papers/surface-complete` coexist. The latter is 33 pages, SHA prefix `e8cc61a1`, commit `21947183`, but its checklist is unmarked. Historical material says the theorem still owed `C(beta,s,epsilon)>0`. | Earlier seals/quarantines are not current approval. Verdict remains `REVIEW-PENDING` pending claim-level and verifier audit. |

## P1: identifiers in repository prose not supported by the frozen author page

These are not automatically "invented" IDs: the exact conclusion is only that
the identifiers/titles are absent from Lluís Eriksson's frozen public author
page and therefore cannot be represented as his published papers without
additional primary evidence.

| Repository location | Unsupported or mismatched reference |
|---|---|
| `docs/legacy/papers/CLOSURE_TREE.md` | `2602.0074` is absent from the frozen author page. |
| `YangMills/ClayCore/BALABAN_CORE_CONTRACT.md` | `2602.0131`, `2602.0134`, and `2602.0135` are absent from the frozen author page. |
| `docs/legacy/UNCONDITIONALITY_ROADMAP.md` | Assigns content to several IDs in `2602.0073`-`2602.0117` that conflicts with their public titles. |

## R29 / `2602.0033`

- Public state: `2602.0033v2`, 8 pages, published on the author page.
- Local proposed replacement: R29, 24 pages, ZIP SHA-256
  `8000c5ef207e0a51c18c6ba7ad47df569d667c4008e9c867646b15ef46205861`.
- R29's own manifest says **nothing was submitted** and keeps `2602.0033`
  `BORRADOR`.
- The manifest's commit `2504ef9d` is not resolvable in the fetched repository.
- Independent forensics confirms the package's binary integrity but finds a P0
  mathematical counterexample and direct page-7 errors. R29 therefore cannot be
  used to relabel the public paper or to claim a ready replacement.

## Local packages are workflow evidence only

- Historical `irreducible-core` ZIPs, including v87, are preserved. v87's own
  report says `cero publicados` and retains an open surface-theorem obligation.
- Three incompatible `ENVIAR-AHORA` generations contain 5, 7, and 8 papers.
  Their presence establishes neither submission nor publication.
- The public census fields remain authoritative until a later frozen capture is
  explicitly recorded with timestamp, URL, and SHA-256.

