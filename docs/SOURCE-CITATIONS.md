# Source Citation System

This repository keeps a structured citation catalog so future workers can look
up primary-source anchors without re-reading noisy OCR or spending context on
already located pages.

The catalog is source metadata only.  It does not copy PDFs, rendered pages, or
long copyrighted passages into the public repository.  It records compact
locators, Lean consumers, local artifact hints, and the current extraction
status.

## Quick Commands

List all citation keys:

```powershell
python scripts\source_citations.py list
```

List entries that are not theorem-feedable yet:

```powershell
python scripts\source_citations.py blockers
python scripts\source_citations.py blockers --status source_pending
```

Show one citation:

```powershell
python scripts\source_citations.py show cmp116.eq231.p-bond-sum
python scripts\source_citations.py show cmp116.eq231.p-family-carrier-source-target
python scripts\source_citations.py show cmp109.ref26.cammarota-infinite-range-cluster
python scripts\source_citations.py show cammarota.cmp85.polymer-mayer-source-target
python scripts\source_citations.py show cmp116.eq237.post-p-resummation
python scripts\source_citations.py show cmp116.constants.c3-alpha5
```

When a citation has already been visually extracted, `show` also prints compact
`extracted claims` so future workers can start from the checked formula shape
instead of re-reading the OCR window.
When a citation or its source metadata contains `web_urls`, `show` prints those
direct targets as well; this is intended for source-pending entries where the
next step is access, not formula transcription.

Search by text or Lean declaration:

```powershell
python scripts\source_citations.py find Eq231
python scripts\source_citations.py lean CMP116Eq231PBondBoundary
```

Check whether the local source packet is present:

```powershell
python scripts\source_citations.py check-local
```

The script resolves artifact hints relative to `YM_SOURCE_ROOT` when that
environment variable is set.  Otherwise it tries the persistent autopilot source
cache:

```text
C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary
```

## Catalog Files

Structured entries live under:

```text
docs/source-citations/*.json
```

Current initial catalog:

```text
docs/source-citations/cmp116-lemma3.json
```

## Entry Status

Use the status field defensively:

| Status | Meaning |
|---|---|
| `visual_confirmed` | Page/equation anchor was visually located, but exact Lean statement may still be open. |
| `ocr_corrupted` | OCR identifies the region but corrupts a formula; open the rendered page/PDF before formalizing. |
| `source_pending` | The entry names the source target and Lean consumer but does not yet provide enough source data. |
| `source_extracted` | The entry has enough exact statement data for a Lean-facing theorem target. |

No entry is a proof.  A citation becomes theorem input only after the
corresponding Lean theorem is implemented and oracle-checked.

`source_pending` entries may also record failed access attempts.  For example,
`cammarota.cmp85.polymer-mayer-source-target` records the DOI/Project Euclid
targets and the reason the currently visible OCR cannot theorem-feed CMP116
Eq. (2.29).  Check that key before re-running broad Cammarota searches.
The key `cmp116.eq231.p-family-carrier-source-target` plays the same role for
the Eq. (2.31) P-family: it records the exact missing carrier/orientation and
counting facts needed before eliminating the remaining source-specific
carrier-containment hypothesis in the concrete finite-bond-set route.  The
generic `CMP116Eq231PBondBoundary` remains available as an internal
combinatorial abstraction.  The filtered-powerset route
`CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets` eliminates
that carrier-containment premise once a caller supplies the exact source
dictionary `PIndex = cmp116Eq231SourcePIndex gapCubes admissible`.  The same
filtered route is also exposed for the weighted post-`P` package and direct
Lemma-3 estimate via
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_filteredBondSets` and
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_filteredBondSets`.
The keys `cmp116.eq237.post-p-resummation` and
`cmp116.constants.c3-alpha5` record the visually confirmed page-20 source
data for the combined post-`P` boundary, the alpha5/C3 region, and Lemma 3's
final amplitude shape.  The Lean Eq. (2.37) consumer
`CMP116Eq237MajorizationBoundary` now turns the seven-delta decay plus residual
budget into the canonical Lemma-3 post-`P` majorization, while the combined
post-`P` source estimate and `Z0/Z0'` source-to-Lean dictionary remain separate
open obligations.  The package-level constructors
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237Majorization` and
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237Majorization`
propagate that source-shaped majorization into the weighted post-`P` Lemma-3
route.
Use `python scripts\source_citations.py blockers` at the start of a source
wake to see all `source_pending` and `ocr_corrupted` entries with their Lean
targets and first open question.

## Why This Exists

The CMP116 Lemma 3 lane currently has strong source-neutral Lean consumers, but
the remaining blocker is exact primary-source extraction around equations
(2.29), (2.31), (2.37), and Lemma 3/(2.38).  The citation catalog lets a worker
ask:

```powershell
python scripts\source_citations.py show cmp116.eq231.p-bond-sum
python scripts\source_citations.py show cmp116.eq231.p-family-carrier-source-target
```

and immediately see:

* the printed/PDF page range;
* rendered-page artifact hints;
* direct web targets, when the catalog has them;
* the relevant local OCR line range;
* the Lean declarations that consume the source statement;
* what remains unsafe to claim.

This is intended to stop repeated broad OCR searches and keep source work
anchored to stable keys.
