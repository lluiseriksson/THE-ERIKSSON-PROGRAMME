# K2 centered-denominator witnesses — favorable diagnostic (2026-07-26)

All five preregistered t-box witnesses passed the centered denominator
condition, and each live/rerun pair was byte-identical:

| index | t-box | uniform denominator floor | live/rerun SHA-256 |
|---:|---|---:|---|
| 0 | `[0,1/50]` | `1.1886689192002117770...` | `B5BF78E72719CF5A...` |
| 50 | `[1,51/50]` | `1.2872343532699265724...` | `B5366E962FCC5E6C...` |
| 100 | `[2,101/50]` | `1.6527343582522120440...` | `E6DC16B0D88C05C5...` |
| 144 | `[72/25,29/10]` | `2.4425373439717848138...` | `537CFE7F7635EFB2...` |
| 156 | `[78/25,157/50]` | `2.8130412420250262109...` | `5A749886A3964F50...` |

Every run used the frozen delta box `[9/1000,1/100]`, midpoint `19/2000`,
half-width `1/2000`, grid `192 x 192`, physical split `1181/1000`, and Arb
precision 140 bits. The full hashes and numerical details are in the ten
committed live/rerun transcripts under `scripts/`.

This is diagnostic conditioning evidence only. It does not establish a
uniform t-cover, the R3 residual inequality, the companion/outer-tail charge,
or any K2/G2/G6/manuscript promotion.
