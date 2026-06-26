# No-new-consumers check

A patch is rejected as cosmetic when all are true:

```text
1. It adds a theorem/constructor whose name ends with `_of_*` or `from_*`.
2. The new theorem still requires the same live source hypothesis.
3. No source package field is discharged.
4. No source DB entry is promoted from source_pending to source_extracted with bounded data.
```

A patch is accepted as real progress when at least one is true:

```text
- A field of `CMP116Eq231BalabanPFamilySourcePackage` is proved or narrowed.
- A Batch 003 proof obligation moves from blocked_on_source to source_extracted/theorem_checked.
- A theorem removes hpointwise, hgeometry, CMP116Eq229Summability, fixed-Z0prime, or an equivalent named live source hypothesis.
```
