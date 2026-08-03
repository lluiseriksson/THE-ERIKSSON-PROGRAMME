# 2601.0115v3 P2 replacement audit

Status: **LISTO-LOCAL**. Owner hold applies: do not upload from this package.

## Scope and defect

- Public object: `2601.0115v2`, 9 pages, unencrypted Letter PDF.
- Frozen public SHA256: `e845b2d9906714b04d525b82ed1c3c53d38238c3377ecb23417a69391a0e1382`.
- Defect: Table 1 on page 6 extends below its 612 x 792 pt MediaBox. MuPDF text tracing finds exactly 152 characters with bounding boxes outside the page, including the final five rows; the lower rule is also outside.
- Risk/action: P2 layout defect; `REPLACE-VERSION` with no change to claims, text, data, figures, references, or pagination.

## Repair

Only page 6 receives the vector transformation

`0.9 0 0 0.9 31.0 106.1 cm`.

The transform uniformly scales and repositions the existing page content. It does not rasterize or reconstruct any text, table, or figure. All MediaBoxes remain 612 x 792 pt. The complete page-6 painted bounds become x = [95.016, 517.293] pt and y = [37.900, 755.960] pt in top-down coordinates, leaving more than 30 pt of safety margin.

## Mechanical verification

- Output: `2601.0115v3-P2-7e32a880d7fb.pdf`.
- Output SHA256: `7e32a880d7fb3d91a64c9c3ede8ea605b480e003ea0693749675fc39ce037546`.
- Pages: 9; encrypted: no; page boxes preserved.
- Source page 6: 152 traced characters outside MediaBox.
- Repaired page 6: 0 traced characters outside MediaBox.
- Page-6 character sequence: all 633 traced characters preserved in order.
- Pages 1-5 and 7-9: pixel-identical to the public v2 at 144 dpi.
- Page 6: pixel-different as intended; Table 1 label and final `I_sum` row are extractable.
- Clean rebuild: byte-identical to the packaged PDF.
- Verifier contains no Python assertion nodes and passes under both normal Python and `python -O`; see the two transcripts in `artifacts/`.

## Visual inspection

All nine pages were rendered with Poppler `pdftoppm` at 140 dpi and inspected page by page.

| Page | Visual result |
|---:|---|
| 1 | PASS - title, abstract, section start, footer and glyphs intact. |
| 2 | PASS - lists, headings, equations and footer intact. |
| 3 | PASS - definitions, displayed equations and proof text intact. |
| 4 | PASS - Hamiltonian definitions, lemma, equations and footer intact. |
| 5 | PASS - artifacts/results text, Figure 1 and caption intact. |
| 6 | PASS - Figures 2-3 and captions legible; Table 1 complete through `I_sum`; lower rule visible; no clipping or overlap. |
| 7 | PASS - discussion, limitations and series-positioning text intact. |
| 8 | PASS - precision, reproducibility and Appendix A content intact. |
| 9 | PASS - appendices, references and footer intact. |

No clipped text, broken glyphs, overlap, corrupt image, or unintended page change was observed in the repaired PDF.

## Decision

`2601.0115v2` -> **REPLACE-VERSION** -> local `2601.0115v3-P2-7e32a880d7fb.pdf`.

The package is `LISTO-LOCAL` for this isolated P2 repair. Submission remains an owner action and should be ordered after all P0/P1 actions in the global audit.
