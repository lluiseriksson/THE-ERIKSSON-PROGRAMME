# Owner submission checklist — no automated submission

This is a hand-off procedure, not permission to submit.  The auditor did not
open a final submission confirmation, upload a file, or press any ai.viXra/arXiv
button.  The literal category, title, author, abstract, comments, change note and
filename for each replacement live in that package's `SUBMISSION-ID.txt`.

## Gate before any click

- Confirm the action row is `REPLACE-VERSION`, not `REVIEW-PENDING`.
- Confirm the package says `LISTO-LOCAL` and contains: final PDF, source, frozen
  public input, build transcript, `python` and `python -O` verifier transcripts,
  independent audit, manifest and immutable GitHub link.
- Recompute SHA-256 and compare it with the manifest and submission sheet.
- Run `pdfinfo` and check pages, `<5 MB`, `Encrypted: no`, and embedded fonts.
- Confirm abstract `<400` words and comments are brief technical metadata.
- Confirm the current public version and its SHA have not changed since the
  2026-07-31 census.  If they changed, stop and recensus that record.
- Use the same email address as the original submission.  Account rotation for
  Fable has no bearing on ai.viXra ownership.
- Follow the causal order in `SUPERSESSION-MATRIX.md`; verify each public result
  before starting the next.

## Exact replacement path

1. Open `https://ai.vixra.org/submit`.
2. Under **Replacements and Withdrawals**, choose **replacement form**.  Do not
   use **submission form**: that path creates a new record.
3. Enter the existing ai.viXra identifier from `PUBLICATION:` exactly, including
   all four digits after the dot.
4. Enter the original-submission email; select the category copied literally
   from `CATEGORY:`.
5. Paste `TITLE:`, `AUTHOR:`, `ABSTRACT:`, `COMMENTS:` and `CHANGE NOTE:` without
   paraphrase.  Recount the abstract after pasting.
6. In the PDF upload control, choose exactly the relative path named by `FILE:`.
   Confirm the browser shows that basename, not an older hash-named build.
7. Review every field against `SUBMISSION-ID.txt`.  Save a screenshot or text
   transcript of this review state.
8. Stop before the final submit/confirmation control.  The owner alone decides
   whether and when to press it.
9. After owner submission, record timestamp, confirmation/reference and status
   as `ENVIADO/PENDIENTE`; do not call it `PUBLICADO`.
10. Only when the public page changes: download the public PDF anew, record direct
    URL, UTC timestamp, SHA-256, size and pages, visually compare all pages, then
    mark `PUBLICADO` or record a discrepancy.

The ai.viXra instructions state that replacements use the replacement form, the
email must match the original submission, earlier versions normally remain
online, abstracts must be under 400 words, comments brief, PDFs under 5 MB, and
rapid/frequent replacements may be rejected.  See `https://ai.vixra.org/submit`.

## New paper / supersession path

The four supersession decisions in the matrix already point to public successor
papers.  They do **not** authorize duplicate uploads.  Preserve the old record as
provenance and use the successor as the authoritative citation.  If ai.viXra
offers no non-upload metadata note, record the relation in repository/public
documentation; do not fabricate a replacement version merely to add a notice.

For a genuinely new paper in the future, use **submission form**, not
**replacement form**, and only after a distinct terminal claim and full audit
show that it is not substantially the same work.  No current audit action needs
that path.

## Per-record owner order

| Order | Record | Expected new version | Package sheet | Stop condition |
|---:|---|---|---|---|
| 1 | 2602.0052v2 | v3 | `output/publication-audit/2602.0052-v3/SUBMISSION-ID.txt` | public identity/title/PDF not restored exactly |
| 2 | 2602.0036v2 | v3 | `output/publication-audit/2602.0036-v3/SUBMISSION-ID.txt` | Ricci/O'Neill withdrawal not public |
| 3 | 2602.0033v2 | v3 | `output/publication-audit/2602.0033-r30/SUBMISSION-ID.txt` | R30 manifest/audit/public SHA mismatch |
| 4 | 2602.0085v1 | v2 | `output/publication-audit/2602.0085-v2/SUBMISSION-ID.txt` | independent audit not passed |
| 5 | 2602.0084v1 | v2 | `output/publication-audit/2602.0084-v2/SUBMISSION-ID.txt` | 0085 not public first or audit not passed |
| 6 | 2602.0035v1 | v2 | `output/publication-audit/2602.0035-v2/SUBMISSION-ID.txt` | any upstream item 1--5 unresolved |
| 7 | 2602.0038v2 | v3 | `output/publication-audit/2602.0038-v3/SUBMISSION-ID.txt` | provenance re-audit/manifest/link absent |
| 8 | 2602.0041v3 | v4 | `output/publication-audit/2602.0041-v4/SUBMISSION-ID.txt` | provenance re-audit/manifest/link absent |
| 9 | 2601.0115v2 | v3 | `output/publication-audit/2601.0115-v3/SUBMISSION-ID.txt` | table/preflight/public comparison mismatch |

At hand-off, the correct terminal instruction remains: **NO ENVIAR TODAVÍA**.
