# Eq. (2.37) citation extraction requests

## Required source packet

```text
source_id: cmp116
primary keys:
  - cmp116.eq237.post-p-resummation
  - cmp116.constants.c3-alpha5
operational route key (repository metadata; not a primary source):
  - crosswalk.eq237.combined-postp-route
required private artifacts:
  - balaban-rg-II-cmp116-1104161193.pdf
  - text/cmp116-pages-15-20.txt
  - renders/cmp116-source-19.png
  - renders/cmp116-source-20.png
```

## Extract exactly

1. The full Eq. (2.37) display with all factors and summation/fiber context.
2. The paragraph before Eq. (2.37) using Eq. (1.28), Eq. (2.29), and epsilon2 smallness.
3. The paragraph after Eq. (2.37), especially adapted Eq. (2.32), half-reserve and `(kappa1-1)/2` condition.
4. The alpha5 and C3 region after Eq. (2.37).

## Record alongside extraction

- Keep `crosswalk.eq237.combined-postp-route` attached to the extracted packet as the public operational route key.
- Preserve the fixed-`Z0'` display plus post-(2.37) final summation as a combined source route to `cmp116PostPResidualSourceBound_of_eq237`.
- Do not promote standalone normalized `Z0` or `Z0'` source theorems unless the private source packet explicitly supports that split.

## Artifact manifest fields

```text
pdf_sha256
text_sha256
render_19_sha256
render_20_sha256
printed_pages
pdf_pages
line_ranges
agent
scan_date
visual_check_notes
```

## Promotion gate

A citation can move to `source_extracted` only when the display, hypotheses, quantifiers, component indexing, constants, combined-route invariant and Lean dictionary target are all written without OCR ambiguity.
