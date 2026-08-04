# Direct Wronskian-sign archive audit — 2026-07-23

The executable audit `scripts/audit_surface_direct_w_sign_cover.py` scans all
CWIN=3/2 manifests, including quarantined ones, but accepts a transcript only
when its production/replay bytes, recorded hashes, row partition, and strict
negative Arb uppers pass the existing parser.

This is deliberately a different claim from G2: the exact algebraic identity
`W^J=exp(-8 beta) W`, together with the independent `F_B>0` theorem, would
turn an exhaustive sign archive into a direct `E'<0` proof. It would not prove
`H_tail`, K2, K4, S1'''/S2''', or G6.

Current result: 333 valid transcripts (six additional records are rejected:
two stale output hashes and four transcripts without the required scaled-domain
headers). The all-status candidate pool reaches beta `[20,1629/16]` but has
overlaps because it includes superseded/quarantined records. Restricting to
`status=current` removes those overlaps, but still leaves these beta gaps:

Two new order-24 seam blocks, `[251/4,63]` and `[63,253/4]`, validate with
212 and 214 rows respectively. They remain quarantined because they are sign
evidence only. A wider brute-force attempt on `[251/4,65]` and a high-order
retry on the narrow seam both timed out; the incidents are recorded separately.
A third quarantined order-24 block, `[97/2,195/4]`, validates with 141 rows
and closes only that all-status quarter-unit seam; it does not alter the
current-status gaps or the G2 relay verdict.

```text
[765/16,69], [625/8,629/8], [80,401/4],
[803/8,1609/16], [805/8,1613/16], [807/8,1617/16],
[809/8,1621/16], [811/8,1625/16], [813/8,407/4],
[1629/16,1000/9].
```

There are also overlapping archived boxes, so the result is not a terminal
direct-sign proof. No manifest or manuscript state was changed.
