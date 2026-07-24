# Incident — G2 gap `[81,401/4]` has no admissible order-40/45 manifests (2026-07-24)

## Observation

`scripts/audit_surface_g2_relay_admissibility.py` currently reports

```
beta_union_complete = false
beta_union_gaps = [
  [765/16,69], [81,401/4], [102,1000/9]
]
```

The audit output has `deficiencies=[]`; the gaps arise because admissible
manifests are absent or skipped, not because a terminal sign row was parsed as
negative.

## Independent checkout search

The repository contains no `run-manifests/*.json` matching `order-40`,
`order40`, `rescue40`, or a beta interval `[81,81.5]` (the search was run from
the current worktree after the audit).  Consequently the claimed order-40/
order-45 chain for `[81,401/4]` is not present as admissible provenance in this
checkout.  Existing high-beta manifests start at `[100.25,100.3125]` and later;
they do not cover this gap.

## Disposition

This gap cannot be closed by changing a status field or relabelling historical
files.  A new preregistered production/replay campaign (or a separately
verified manifest imported with complete provenance) is required.  Until then
G2 remains `BLOCKED`, with no G2/G6 or manuscript promotion.
