# Closed-loop execution model

v5 treats every agent output as a candidate patch with a measurable delta.

```text
mission contract -> source/router prompt -> patch intake -> patch score ->
contract check -> build/oracle evidence -> proof-card update
```

## Patch delta

```text
Delta = {
  removed_fields,
  source_promotions,
  theorem_checked_promotions,
  toy_theorems,
  new_consumers_without_removed_fields,
  new_opaque_props,
  core_import_violations,
  ocr_constant_uses,
  tautological_admissible_defs
}
```

The default acceptance score is:

```text
10*removed_fields
+ 8*theorem_checked_promotions
+ 6*source_promotions
+ 4*toy_theorems
- 8*new_consumers_without_removed_fields
- 6*new_opaque_props
- 20*core_import_violations
- 12*ocr_constant_uses
- 12*tautological_admissible_defs
```

Accept only if score is at least 10 and the patch has at least one real positive
delta.
