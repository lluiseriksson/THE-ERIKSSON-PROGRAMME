# Patch intake guide v5

Every proposed patch must have an intake JSON.  The intake is not bureaucracy;
it is the bridge between mission contracts, source keys, Lean targets and proof
card status.

## Required fields

- `contract_id`
- `proof_card`
- `source_keys_touched`
- `lean_targets_touched`
- `removed_fields`
- `source_promotions`
- `new_consumers_without_removed_fields`
- `new_opaque_props`
- `verification_evidence`
- `remaining_blockers`

## Minimal useful intake

A failed source extraction can still be useful if it narrows the blocker.  In
that case set all positive deltas to zero and write the exact missing source
field under `remaining_blockers`.  Do not create a theorem-shaped wrapper for a
missing source fact.
