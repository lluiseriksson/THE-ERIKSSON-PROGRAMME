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

Show one citation:

```powershell
python scripts\source_citations.py show cmp116.eq231.p-bond-sum
```

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

## Why This Exists

The CMP116 Lemma 3 lane currently has strong source-neutral Lean consumers, but
the remaining blocker is exact primary-source extraction around equations
(2.29), (2.31), (2.37), and Lemma 3/(2.38).  The citation catalog lets a worker
ask:

```powershell
python scripts\source_citations.py show cmp116.eq231.p-bond-sum
```

and immediately see:

* the printed/PDF page range;
* rendered-page artifact hints;
* the relevant local OCR line range;
* the Lean declarations that consume the source statement;
* what remains unsafe to claim.

This is intended to stop repeated broad OCR searches and keep source work
anchored to stable keys.
