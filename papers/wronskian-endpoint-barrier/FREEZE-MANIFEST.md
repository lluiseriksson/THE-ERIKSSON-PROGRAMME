# Freeze manifest

Capture date: 2026-08-04

Branch: `codex/wronskian-reduction-51`

Parent before the paper changes: `fea74f3766b9c78a440d08d73f04e1973cfeaacc`

Capture method: filesystem byte length from `Get-Item`; SHA-256 from
PowerShell `Get-FileHash -Algorithm SHA256`; line-ending counts from raw-byte
counts of `0x0a` (LF) and `0x0d` (CR). PDF line-ending counts are not
semantically meaningful and are omitted below.

| Artifact | Bytes | SHA-256 | LF | CR |
|---|---:|---|---:|---:|
| `wronskian_endpoint_barrier.tex` | 21,978 | `f72646e1d01ada72a5c1aa0d0f876700affef61ba9b3fe4f52d6ad8e9c15d94b` | 562 | 0 |
| `wronskian_endpoint_barrier.pdf` | 353,794 | `6ddb421040fc0089568550e3e893c3d2df688ed28127e6ca31cec2ba3aaaf507` | - | - |
| `README.md` | 1,039 | `811a7d545b932190603def736b71a4cd47851ebf25715057902cf6727cd2298b` | 27 | 0 |
| `VERIFICATION.md` | 2,410 | `be1a8ccf3aa6edab6554536d94ebcc36f48a50c3a6e27abdf7914374fea2e01d` | 62 | 0 |
| `scripts/wronskian_endpoint_kill_test.py` | 9,696 | `b456b88def90c52cd654f39abd1f139155dbead8404fc641f9a21441c0ac0c83` | 281 | 0 |
| `docs/WRONSKIAN-REDUCTION-51-RESULT.md` | 10,635 | `722d70b3834e81a2521ffcbdd71b0fa86eb936f51bc1dfd161468be2855475d3` | 292 | 0 |
| `output/pdf/wronskian_endpoint_barrier.pdf` | 353,794 | `6ddb421040fc0089568550e3e893c3d2df688ed28127e6ca31cec2ba3aaaf507` | - | - |

The two PDF paths are byte-identical. The final Git commit SHA is reported in
the handoff after commit creation. No external audit or self-certifying
correctness verdict is attached to this freeze; it records the object and the
attacks attempted.
