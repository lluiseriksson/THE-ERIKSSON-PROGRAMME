# Batch 004 — Eq. (2.31) source-package live-field index

This patch is intentionally safe for a repository that has already moved past Batch 003.
It adds new files only; it does not overwrite `scripts/source_db.py`, existing catalogs, Lean files, or generated SQLite.

After copying into the repo, run:

```powershell
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py show proof.eq231.field.bond-fst-mem-gapCubes
```

Main new files:

```text
docs/source-db/catalogs/eq231-source-package-live-fields.json
docs/source-db/indices/EQ231-SOURCE-PACKAGE-LIVE-FIELDS.md
docs/source-db/indices/EQ231-FIELD-DISCHARGE-PROMPTS.md
docs/source-db/indices/EQ231-SOURCE-DICTIONARY-COMMIT-QUEUE.md
docs/source-db/indices/EQ231-CITATION-EXTRACTION-REQUESTS.md
docs/source-db/reports/BATCH-004-EQ231-SOURCE-PACKAGE-LIVE-FIELDS.md
```
