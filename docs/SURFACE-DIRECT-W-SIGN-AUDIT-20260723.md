# Direct Wronskian-sign archive audit — 2026-07-23

The executable audit `scripts/audit_surface_direct_w_sign_cover.py` scans all
CWIN=3/2 manifests, including quarantined ones, but accepts a transcript only
when its production/replay bytes, recorded hashes, row partition, and strict
negative Arb uppers pass the existing parser.

This is deliberately a different claim from G2: the exact algebraic identity
`W^J=exp(-8 beta) W`, together with the independent `F_B>0` theorem, would
turn an exhaustive sign archive into a direct `E'<0` proof. It would not prove
`H_tail`, K2, K4, S1'''/S2''', or G6.

Current result: 328 valid transcripts (six additional records are rejected:
two stale output hashes and four transcripts without the required scaled-domain
headers), beta component `[20,1629/16]`, but no exact tiling. The audit reports
these gaps:

```text
[89/4,31], [497/16,63/2], [97/2,52], [833/16,225/4],
[113/2,125/2], [251/4,253/4], [127/2,255/4], [64,257/4],
[129/2,259/4], [625/8,401/4], [803/8,1609/16],
[805/8,1613/16], [807/8,1617/16], [809/8,1621/16],
[811/8,1625/16], [813/8,407/4], [1629/16,1000/9].
```

There are also overlapping archived boxes, so the result is not a terminal
direct-sign proof. No manifest or manuscript state was changed.
