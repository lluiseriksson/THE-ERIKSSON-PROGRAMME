# Batch 006 integration brief for v6

Batch 006 added an operational live-field map for the Gaussian/root/Hessian/activity/H# stack.
This pack turns that map into executable mission contracts.

## Main invariant

```text
final bound / H# identity != proof of Gaussian/root/Hessian/source dictionary
```

## Agent rule

Choose exactly one field from `data/batch006_live_field_map.v6.json`.  A patch
that touches a downstream field while claiming to close an upstream field must
supply a separate source theorem for the upstream field, or it fails the
anti-backfill audit.
