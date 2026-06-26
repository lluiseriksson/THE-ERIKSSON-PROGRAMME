# LLM fast-context update — Batch 007

After Eq. (2.31), Eq. (2.29), and Gaussian/root/Hessian live-field maps, the next post-P source frontier is CMP116 Eq. (2.37).

## Read these cards

```text
proof.eq237.live-fields.v2
proof.eq237.fixed-z0prime-display.v2
proof.eq237.post-summation.final-z0prime.v2
proof.eq237.z0-z0prime-dictionary.v2
proof.eq237.constant-majorants.alpha5-c3.v2
guard.eq237.no-unsourced-splitting.v2
```

## One-sentence state

Lean has theorem-generated consumers for the combined Eq. (2.37) route; the remaining work is source extraction of the fixed-`Z0'` estimate, final post-(2.37) summation, dictionaries, component product and constants.

## Do next

```text
python scripts/source_db.py show proof.eq237.live-fields.v2
python scripts/source_db.py show proof.eq237.fixed-z0prime-display.v2
python scripts/source_db.py show proof.eq237.post-summation.final-z0prime.v2
python scripts/source_citations.py show cmp116.eq237.post-p-resummation
python scripts/source_citations.py show cmp116.constants.c3-alpha5
```
