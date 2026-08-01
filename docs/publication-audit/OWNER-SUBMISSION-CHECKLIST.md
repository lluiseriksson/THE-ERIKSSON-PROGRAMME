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
- For a supersession replacement, confirm the abstract begins with the exact
  uppercase headline printed on PDF page 1 and that page 2 separates retained,
  superseded and successor claims.
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

## Supersession replacement path

The four supersession decisions in the matrix already point to distinct public
successor papers. Under the owner's 2026-08-01 policy, make that claim relation
visible by replacing the **old** record with its audited notice version. Use the
replacement form; do not upload the successor again and do not create a new
record. The old manuscript remains after the two-page notice as provenance.

Paste the literal uppercase `SUPERSEDED BY ...` headline at the start of the
abstract. A supersession notice is not a blanket retraction: retain every exact
old claim that survives, identify only the affected claim class, and name the
successor that supplies the corrected or extended result. `2607.0089v1` remains
`REVIEW-PENDING` even though it is the named successor of `2607.0023v1`.

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
| 4 | 2602.0085v1 | v2 | `output/publication-audit/2602.0085-v2/SUBMISSION-ID.txt` | local PDF/package hash differs from its audited manifest |
| 5 | 2602.0084v1 | v2 | `output/publication-audit/2602.0084-v2/SUBMISSION-ID.txt` | 0085 not public first or local manifest mismatch |
| 6 | 2602.0035v1 | v2 | `output/publication-audit/2602.0035-v2/SUBMISSION-ID.txt` | any upstream item 1--5 unresolved |
| 7 | 2602.0038v2 | v3 | `output/publication-audit/2602.0038-v3/SUBMISSION-ID.txt` | provenance phrase or package hash differs from its audit/manifest |
| 8 | 2602.0041v3 | v4 | `output/publication-audit/2602.0041-v4/SUBMISSION-ID.txt` | conditional-scope phrase or package hash differs from its audit/manifest |
| 9 | 2601.0115v2 | v3 | `output/publication-audit/2601.0115-v3/SUBMISSION-ID.txt` | table/preflight/public comparison mismatch |
| 10 | 2512.0073v1 | v2 | `output/publication-audit/2512.0073-v2/SUBMISSION-ID.txt` | exact omega=0 retention or final release hash differs |
| 11 | 2601.0047v2 | v3 | `output/publication-audit/2601.0047-v3/SUBMISSION-ID.txt` | consolidation is described as refutation or final hash differs |
| 12 | 2607.0035v1 | v2 | `output/publication-audit/2607.0035-v2/SUBMISSION-ID.txt` | reduced/original-edge boundary or final hash differs |
| 13 | 2607.0023v1 | v2 | `output/publication-audit/2607.0023-v2/SUBMISSION-ID.txt` | independent-replay-pending status or final hash differs |

Items 1--9 were reported by the owner as sent on 2026-08-01 and remain
`ENVIADO/PENDIENTE` until their public pages and PDFs are independently checked.
Do not resend them. Items 10--13 are a separate owner sequence.

At hand-off, the correct terminal instruction remains: **NO ENVIAR TODAVÍA**.
