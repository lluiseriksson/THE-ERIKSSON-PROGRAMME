# C6d localized retained tower — cold root failure

- Source SHA: `e44b164c59aa289bb1ca2995bc71dfe7e5f58ef9`
- Runner revision: `c6d-localized-retained-tower-cold-v8`
- Mathlib SHA: `07642720480157414db592fa85b626dafb71355b`
- Focal: exit `0`, `1978.080 s`
- Audit: exit `0`, `20.887 s`
- Root: exit `1`, `9380.972 s`
- Runner-reported evidence digest: `eba9387062c7c0a0cfe10b883b3e6bd325e8c05e5601cd7e5117ef24b70a4bf9`
- Downloaded `evidence.json` SHA-256: `43abdd0bfcca3b3f7dd9c9be9962ed92768561b7d95c758655c45730d128ca5c`
- Downloaded archive SHA-256: `0617ba6be7f7718b09e863f9dbdebb77fd4add8a67591e868549ce6ef3171d37`

First real root error:

```text
YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTower.lean:45:25:
typeclass instance problem is stuck
  NeZero ?m.167
```

The later failures at lines 73–77 are elaboration cascades from this first
error. This package is failure evidence only: it does not retract the focal or
audit PASS, and it is not a root seal.
