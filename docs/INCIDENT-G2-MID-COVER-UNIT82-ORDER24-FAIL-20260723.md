# Incident: order-24 mid-cover unit 82 reaches the subdivision wall

**Unit:** `[275/4,69]` (index 82)  
**Contract:** CWIN `3/2`, beta order `24`, t order `25`, 180-bit Arb,
`min_dt=1/100000`  
**Scope:** candidate finite-beta sign bridge; no G2/G6 or `(H_tail)` promotion.

The order-24 extension-5 driver was run after preregistration. It produced
strict-negative rows for units 79–81, then failed on unit 82 at the frozen
minimum angular width:

```text
order22 repair cover failure near t=3.1178733989897687
```

No unit-82 transcript or manifest is admitted. The failure is an execution
boundary, not a sign result. Units 79–81 require their independent replay
before they can be included in the extension-5 geometric audit. The remaining
unit `[275/4,69]`, the finite-bridge relay lemma, and the G2/G6 seals remain
open.
