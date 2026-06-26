# C12 — Non-vacuity audit campaign

Goal: ensure source-shaped packages do not become true only because the index family is empty.

Audit witnesses:
- `∃ Z, DIndex Z`.
- `∃ Z D, D ∈ DIndex Z ∧ PIndex Z D`.
- `∃ P, P.Nonempty` when lower-cardinality or decay-from-size is used.

This should live in docs/audits or experimental packages, not as a burden on every consumer theorem.
