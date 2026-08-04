# (46) Freeze record — Birkhoff–Dobrushin y muro

Freeze status: **fabrication target, not external verdict**.

- Branch: `codex/candidate-46-birkhoff-dobrushin-wall`
- Base `main`: `12bf6e241694aa5cfb5c7a6e08a96c8fa47ff9b1`
- Capture host: Windows owner desktop, isolated worktree
- Capture method: `System.IO.File.ReadAllBytes`, UTF-8 decode, explicit
  normalization to LF and CRLF, and
  `System.Security.Cryptography.SHA256.HashData`
- Kill-test: one Python process at a time, standard library only, no GPU
- Normal run: exit `0`, 225 ms, sampled peak working set 13,668,352 bytes
- Optimized run: exit `0`, 290 ms, sampled peak working set 17,801,216 bytes
- Lean/Lake/oracle: not invoked
- External audit: not performed; no terminal verdict is claimed here

## Frozen body

| Path | Raw/LF bytes | SHA-256 raw/LF | CRLF bytes | SHA-256 CRLF |
|---|---:|---|---:|---|
| `docs/CANDIDATE-46-BIRKHOFF-DOBRUSHIN-WALL.md` | 11130 | `0e94f9be5b5adc2a7be7972fde286d2b31a23fc596348a540992f85398655b34` | 11417 | `f011ec5fd7cad70581c906ae0e657683bf10b6d5e1b826daa40fb7d838a87ca6` |
| `docs/CANDIDATE-46-KILLTEST-TRANSCRIPT.json` | 1599 | `b5472762dcc462d05fd70531dec74c7091e342102a01e4fb1092f618ab185e20` | 1662 | `1c3ac33db2c926e7e36f0bc827095c096a739895ec20ac012e8423bca703cf6b` |
| `scripts/killtest_birkhoff_tensor_wall.py` | 2679 | `b0bd9f744331acdf769b194d922e75bcff7f64d15709904584cfe85526729412` | 2763 | `cebcb22f2da82be389dd62f7598bd9f679141612105484d9fadb0cb49aa146f9` |

The raw files were LF at capture time, so raw and LF hashes coincide. The Git
commit containing this record is the branch freeze SHA; record it together with
these body hashes when handing the object to an external audit.

## Attacks attempted

1. Exact brute-force enumeration of all projective cross-ratios for
   (K^{\otimes L}), (L=1,2,3,4).
2. Comparison with the factorized prediction (Theta_L=9^L).
3. Exact comparison of the Birkhoff coefficient
   ((3^L-1)/(3^L+1)) with the volume-independent product spectral ratio
   (1/2).
4. Repetition under `python -O`, where deleted `assert` statements cannot turn
   a failing check into a false pass; the harness uses explicit exceptions.
5. Convention audit: Dobrushin's 1956 overlap coefficient is recorded as
   (1-\delta), not silently identified with the modern contraction
   coefficient (delta).
6. Scope attack: global oscillation of a product is explicitly excluded from
   the volume-uniform Dobrushin claim; only coordinate oscillations and the
   interdependence window are claimed uniform.
