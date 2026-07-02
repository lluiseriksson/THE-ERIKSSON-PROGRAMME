# Cammarota CMP85 acquisition and citation ledger

## Known metadata

```text
Camillo Cammarota,
Decay of correlations for infinite range interactions in unbounded spin systems,
Communications in Mathematical Physics 85, 517-528 (1982),
DOI 10.1007/BF01403502.
```

Springer metadata confirms the title, author, journal, pages, DOI, abstract-level polymer-model relevance, and references. It does not expose the theorem text without access.

## Failed or insufficient paths already known

```text
Project Euclid full/PDF endpoint: automation has seen Incapsula/anti-bot HTML.
2026-06-28 direct Project Euclid current-PDF attempt:
  https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-85/issue-4/Decay-of-correlations-for-infinite-range-interactions-in-unbounded-spin/cmp/1103921545.pdf
  returned a 1164-byte anti-bot HTML body, SHA-256
  6368CFB9639DC2FB996F149B82D7D3F45C19882640E1C15E97571458562D81B3,
  not a usable PDF artifact.
Project Euclid legacy endpoint from DML/Mathdoc:
  https://projecteuclid.org/download/pdf_1/euclid.cmp/1103921545
  also returns HTML/anti-bot content in the automation environment.
Springer page: metadata and abstract only unless institutional/subscription access is available.
Springer guessed PDF endpoint:
  https://link.springer.com/content/pdf/10.1007/BF01403502.pdf
  returns HTML rather than a PDF in the automation environment.
DML/Mathdoc item page:
  http://dml.mathdoc.fr/item/1103921545/
  exposes metadata and the legacy Euclid links, but not an independent local PDF.
ResearchGate/OCR: not acceptable for constants without visual primary check.
```

## Required private artifacts

```text
source-packets/private/cammarota_cmp85/cammarota-cmp85.pdf
source-packets/private/cammarota_cmp85/text/cammarota-cmp85.txt
source-packets/private/cammarota_cmp85/renders/cammarota-theorem1-page-*.png
source-packets/manifests/cammarota-cmp85-artifacts.json
```

Each artifact should have SHA-256, bytes, scan date, page range, and source URL/access note.

## Local artifact check — 2026-07-02

The repo currently contains `source-packets/manifests/batch-005-eq229-cammarota-live-fields.json`, but that file is only the batch-005 operational metadata manifest for the Eq229/Cammarota live-field cards. It is not the required Cammarota primary-source artifact manifest, and it does not certify theorem text, page renders, constants, or hypotheses.

Missing primary-source artifacts remain:

```text
source-packets/private/cammarota_cmp85/cammarota-cmp85.pdf
source-packets/private/cammarota_cmp85/text/cammarota-cmp85.txt
source-packets/private/cammarota_cmp85/renders/cammarota-theorem1-page-*.png
source-packets/manifests/cammarota-cmp85-artifacts.json
```

No theorem extraction, D-family dictionary, smallness threshold, metric convention, or Eq. (2.29) source discharge is claimed by this ledger note.

## Archive holdings note — 2026-07-02

Archive cycle 51 reports that the private Archive lane holds all four
Cammarota CMP85 artifact classes: the paywalled/private PDF
`primary-pdfs\cammarota\cammarota-cmp85-decay-correlations-1982.pdf`, OCR under
`ocr\cammarota-cmp85-decay-correlations-1982\`, twelve page renders, and
`constructor-packets\CAMMAROTA-CMP85-POLYMER-MAYER-PACKET.md`.

This is an acquisition-status improvement only. The public repo paths listed
above remain missing, the private scan must not be committed, and the equation
bodies/theorem constants/hypotheses still require visual extraction before
Eq. (2.29), `CMP116Eq229Summability`, or any D-family dictionary can be
theorem-fed.

## First visual premise field — 2026-07-02

Using the Archive-private render for printed p.517, Theorem 1's first premise
field is now recorded in the source-db as
`cammarota.theorem1.eq1.4.potential_decay`:
`|Phi_xy(S_x,S_y)| <= exp(-delta(x,y)) * J(x,y) * v_x(S_x) * v_y(S_y)`.

This is a one-field visual extraction only. The theorem conclusion, smallness
conditions, constants, Mayer/polymer convergence statement, finite-volume
uniformity, and the CMP116 D-family dictionary remain open, and no private scan
or render is committed to the repository.
