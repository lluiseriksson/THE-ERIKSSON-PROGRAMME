## What changed

- merges published `main` at `40d5f59af88629a9cbadd5e8742bb7d97b11fc7d` through merge commit `2180819b92d36eee716ac983472aab066b638e90`, without rebasing or squashing;
- preserves the measured 300-second outer MCP transport ceiling, its PR #35 evidence, unchanged gate criteria, role separation, re-blinding, and sealed phased synthesis;
- adds three incident-paid operational rules: freeze branch and PR body during external reading, remove or explicitly report disposable clones, and name the byte regime of every textual hash;
- separates normative text in the operational charter from one compact 2026-08-02 incident-provenance record; and
- versions this exact PR-body freeze and its LF/CRLF SHA-256 manifest for external review.

## Incident provenance

- PR #51 moved from dispatched SHA `dae703ddb5e5d0f71e14bfd147c781f530d736cd` to `8eb733ddd54eeb28849cdfa8d9d8e7c09c6d0363` through a five-line charter commit while an external reading was in flight; the reader detected the mismatch and stopped without a verdict.
- Nine disposable audit clones had accumulated. Eight dead `pr39-*` clones were removed in a controlled cleanup; one exact path remains blocked by policy:

CLEANUP-PENDING: C:\Users\lluis\AppData\Local\Temp\pr51-audit-b3c68b391c264c698ebb93d5240e4492

- The frozen PR #51 body differed by 68 CRLF conversions and matched after LF normalization. The incident record preserves the reported body and baseline SHA-256 pairs for both byte regimes.

## Evidence boundary and impact

The new provenance is an incident report, not an independently certified audit transcript. This branch does not edit or certify PR #51, PR #44, or PR #54, and it authors no mathematical or Lean change. The merge commit incorporates the already-published `main` history unchanged.

## Validation

- `git diff --check`
- `python scripts/check_consistency.py` (lightweight repository consistency check; no Lean, Lake, or Colab run)

## External review object

- canonical body file: `docs/audit-artifacts/pr49-body/PR49-BODY-FREEZE-20260802.md`
- capture and byte-regime manifest: `docs/audit-artifacts/pr49-body/PR49-BODY-FREEZE-20260802.txt`
- an external commission and verdict must name the exact reviewed HEAD and the body-capture method, representation, normalization, and hash from that manifest
