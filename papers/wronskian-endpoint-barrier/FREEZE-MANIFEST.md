# Freeze manifest

Capture date: 2026-08-04

Branch: `codex/wronskian-reduction-51`

Predecessor paper commit before specialist-review hardening:
`4c825bcfd8b988e73290ba85e1597a5aaec2ff8e`

Capture method: filesystem byte length from `Get-Item`; SHA-256 from
PowerShell `Get-FileHash -Algorithm SHA256`; line-ending counts from raw-byte
counts of `0x0a` (LF) and `0x0d` (CR). PDF line-ending counts are not
semantically meaningful and are omitted below.

| Artifact | Bytes | SHA-256 | LF | CR |
|---|---:|---|---:|---:|
| `wronskian_endpoint_barrier.tex` | 27,228 | `cd702cb3c54a952bb5f8002b64be699e6822ab9d1e7e1c857e969dd1f73fd989` | 710 | 0 |
| `wronskian_endpoint_barrier.pdf` | 398,436 | `c51cd46c1dc577e4d3bb6f2e36df748e715d2e6dc614c7290d8e9837d92986be` | - | - |
| `README.md` | 1,296 | `b0da260a6ef5bc1c77273a380dfabaca5e62898722ab43a8e1a7fbfd6f4fa04b` | 32 | 0 |
| `VERIFICATION.md` | 3,359 | `3394438e8c8f09c1369d6a1c6c82edefa99947d06d40c5ca3a59df85cd35cb32` | 82 | 0 |
| `scripts/wronskian_endpoint_kill_test.py` | 10,125 | `2eb10e61dd508a71eedbe69dd60de69da64ee7a685ff1597aa3c6beba876d017` | 296 | 0 |
| `docs/WRONSKIAN-REDUCTION-51-RESULT.md` | 11,506 | `b4c1b254f761da979037ba8a9af9c3d06dcd233bdd04301caf253bf7d38609b9` | 307 | 0 |
| `output/pdf/wronskian_endpoint_barrier.pdf` | 398,436 | `c51cd46c1dc577e4d3bb6f2e36df748e715d2e6dc614c7290d8e9837d92986be` | - | - |

The two PDF paths are byte-identical. The final Git commit SHA is reported in
the handoff after commit creation. No external audit or self-certifying
correctness verdict is attached to this freeze; it records the object and the
attacks attempted.
