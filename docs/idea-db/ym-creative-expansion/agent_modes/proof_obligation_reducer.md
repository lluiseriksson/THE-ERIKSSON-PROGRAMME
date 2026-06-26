# Agent mode — proof obligation reducer

Input: one Batch 003 `proof.*` key.

Output:

1. exact live hypothesis to remove;
2. smallest theorem shape that removes it;
3. source keys to inspect;
4. Lean declarations affected;
5. forbidden shortcuts;
6. patch verdict: `source-field-removal`, `honest-interface`, or `cosmetic-reject`.

Rules:

- Never broaden to a neighbouring proof card during the same attempt.
- Never add downstream consumers unless the selected source field is removed.
- Treat `crosswalk.*` and `proof.*` as navigation, not evidence.
