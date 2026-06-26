# Patch Review Rubric — v4

Score candidate patches before integration.

| Signal | Points |
|---|---:|
| Removes one exact theorem/source-package field | +10 |
| Promotes one citation to source_extracted with complete metadata | +6 |
| Adds a pure toy theorem outside core that falsifies/clarifies a blocker | +4 |
| Adds only docs that narrow a blocker | +3 |
| Adds a downstream consumer while old hypotheses remain | -8 |
| Defines source predicate tautologically | -20 |
| Uses lower bound on `|P|` as carrier upper bound | -20 |
| Collapses different `O(1)` constants without majorant theorem | -8 |
| Uses final bound to prove termwise estimate | -20 |

Accept only if:

```text
score >= 10
and (removed_fields + source_promotions) >= 1
```

or if the patch is explicitly a blocker-sharpening commit and changes no Lean consumers.
