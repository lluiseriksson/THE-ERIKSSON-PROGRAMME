# Raw-source M3 field order — Batch 006

This file is a short guardrail for agents working near `BalabanCMP116SourceTheorem.lean`.

## Correct dependency order

```mermaid
flowchart TD
  A[covariance_root_certificate] --> B[root_localization]
  A --> C[gaussian_pushforward]
  C --> E[rawSource package]
  B --> E
  D[wilson_hessian_identification] --> E
  F[local_physical_activity_construction] --> E
  G[raw_pointwise_decay] --> E
  F --> H[support + measurability]
  H --> I[Appendix-F H# consumer]
  E --> I
  I --> J[rooted_hsharp_remainder_identity]
  J --> K[Rsc / flow / IR frontier]
```

## Review checklist

Before approving a source commit, ask:

1. Which exact field disappears?
2. Which primary source page/equation proves it?
3. Are constants and normalizations carried explicitly?
4. Is Dimock being used only as architecture unless a YM dictionary theorem is supplied?
5. Does the commit avoid backfilling upstream fields from downstream bounds?
