# Batch 002 — LLM Context Graph and Operational Indices

Date: 2026-06-26

Batch 002 does not claim new primary-source theorems. It systematizes the
existing source database into fast LLM-facing indices and adds an operational
crosswalk catalog that is searchable through SQLite.

## Added

- Operational crosswalk catalog: `docs/source-db/catalogs/llm-operational-crosswalk.json`.
- Formula registry: JSON, Markdown and CSV.
- Lean ↔ source crosswalk: JSON and Markdown.
- Blocker matrix: JSON and Markdown.
- Paper coverage matrix: JSON and Markdown.
- Symbol dictionary seed: JSON and Markdown.
- Dependency graph: JSON, Mermaid and Markdown.
- Fast context brief for future agents.

## Database counts after batch 002

These are the standalone package counts before merging into the current
repository source database:

- Sources: 14
- Citation/crosswalk records: 46
- Claim/formula records: 110
- Lean target links: 102
- Open questions: 68

Installed at repository HEAD, after rebuilding `docs/source-db/source_index.sqlite`
with the pre-existing catalogs plus the updated operational crosswalk:

- Sources: 14
- Citation/crosswalk records: 50
- Claim/formula records: 154
- Lean target links: 231
- Open questions: 104
- SQLite SHA256: `a91355c59aa3f068392261627a0534b7e2308ca549dc496fff4ccc339a52b5dd`

## Citation status distribution

- `lean_linked`: 8
- `located`: 2
- `ocr_corrupted`: 1
- `source_extracted`: 18
- `source_pending`: 7
- `visual_confirmed`: 10

## Important honesty boundary

The eight `crosswalk.*` records are navigation indices. They are **not** primary
mathematical sources and they deliberately use `source_verified=false` for
route-target formulas. Use them to find the relevant source citation keys and
Lean declarations quickly; do not cite them as proof.

## Main conclusions encoded

1. Eq. (2.31) closes only after the source membership iff and source-carrier identification are proved; the repository already names the four-direction carrier count.
2. Eq. (2.29) needs Cammarota's exact theorem, constants and D-family dictionary.
3. Eq. (2.37) should remain a combined post-P route.
4. Dimock Appendix F requires Omega-connectivity.
5. R-operation source bounds are polymer-local, not bare scalar geometric claims.
6. Flow and IR must stay as separate lanes.

## Validation commands

```text
python scripts/source_db.py verify
python scripts/source_db.py build
python scripts/source_db.py stats
python -m pytest -q
```
