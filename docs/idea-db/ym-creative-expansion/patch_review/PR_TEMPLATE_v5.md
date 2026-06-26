# PR template — hypothesis-removal patch

## Mission

- Contract ID:
- Proof card:
- Source keys:
- Lean targets:

## Positive delta

- Removed fields:
- Source promotions:
- Theorem-checked promotions:
- Toy theorems:

## Negative delta

- New downstream consumers without removed fields:
- New opaque props:
- Core import violations:
- OCR constant/sign/exponent uses:
- Tautological admissible definitions:

## Evidence

- `lake build YangMillsCore`:
- `lake env lean oracle_check.lean`:
- `python scripts/source_db.py verify`:

## Remaining blockers

List the exact source/theorem field still missing.  Do not say “hRpoly remains”
without naming the next smaller field.
