# (46) Freeze record — Birkhoff–Dobrushin y muro

Freeze status: **fabrication target, not external verdict**.

The paper-level freeze below supersedes the earlier calculation-only body for
the scope of candidate (46). The earlier hashes remain useful provenance for
the preregistered kill test.

The earlier commit `da2695a9d2c91b2fce0f7b18d0273e3f4966374a` is **not** an
audit target: a post-commit control-character scan found that the patch
transport had interpreted three inline `\\tanh` sequences as tab escapes and
had stripped several inline TeX delimiters. The mathematics and executable
were unchanged, but the rendered body was defective. This record supersedes
that commit without rewriting history.

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
| `docs/CANDIDATE-46-BIRKHOFF-DOBRUSHIN-WALL.md` | 11151 | `c2784a968550418ae02f2be1390a835b9b739cbb3512981ff568ec03f4b9b064` | 11439 | `ac5d7aea58ac2413af3b785415726998e0f24dd27144f7e1ab8ae00b77b5448e` |
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
7. Body-integrity attack: scan for tab/control characters and malformed inline
   TeX. It rejected the first freeze commit and forced this superseding commit.

## Paper-level freeze (August 4, 2026)

Freeze status: **complete fabrication object; external mathematical and
priority verdict still required**.

- Branch: codex/candidate-46-birkhoff-dobrushin-wall
- Frozen paper-body commit:
  70c0648031ff4f6a00cda572edc26b5ecd0bf59a
- Base main: 12bf6e241694aa5cfb5c7a6e08a96c8fa47ff9b1
- Capture host: Windows owner desktop, isolated worktree
- Capture method: System.IO.File.ReadAllBytes, UTF-8 decode for text,
  explicit normalization to LF and CRLF, and
  System.Security.Cryptography.SHA256.HashData
- PDF compiler: Tectonic, exit 0, 4.063 s wall, sampled peak working set
  196.41 MiB; the only stderr diagnostic was the host Fontconfig default-file
  warning, and the LaTeX log contained no warnings, undefined references,
  overfull boxes, or errors
- Visual QA: Poppler pdftoppm, 140 dpi, all 9 rendered pages inspected;
  one literal qquad transport defect was found, fixed, recompiled, and its
  affected page re-inspected
- Certificate runs: one Python process at a time; normal exit 0, 0.489 s,
  13.39 MiB sampled peak; optimized exit 0, 0.508 s, 18.05 MiB sampled peak
- Lean/Lake/oracle: not invoked
- Colab Pro+: not opened, so no runtime-close event was required
- Fable/Claude: not invoked; the account check exposed
  luis.ebikeride@gmail.com, not the binding account
  masterythief@gmail.com
- External audit: not performed; this record is not a terminal verdict

### Frozen paper body

| Path | Raw/LF bytes | SHA-256 raw/LF | CRLF bytes | SHA-256 CRLF |
|---|---:|---|---:|---|
| papers/birkhoff-dobrushin-wall/birkhoff_dobrushin_wall.tex | 26064 | 23fac8868c4523609f007ad903dda1ed89e4fa129de09118c5f4fbd629774214 | 26705 | e1ad3b2638dd0654f616e548a36c726cb0585f1dd8ff4644325c2e6a7edbda66 |
| scripts/certify_birkhoff_dobrushin_comparison.py | 5803 | 4d677c431d63721710e15b39bd1472149c5e9487b0b6d7010d8963be782fdbde | 5981 | a35806ca0eeee6c480f88104fcba4827e0f1490b6495bdf74796289a88970afa |
| scripts/killtest_birkhoff_tensor_wall.py | 2679 | b0bd9f744331acdf769b194d922e75bcff7f64d15709904584cfe85526729412 | 2763 | cebcb22f2da82be389dd62f7598bd9f679141612105484d9fadb0cb49aa146f9 |
| docs/CANDIDATE-46-BIRKHOFF-DOBRUSHIN-WALL.md | 11954 | 27657f5934440d9c438e9fd74061641334251303f62c8fd0094f567b58272198 | 12255 | 750d5ae71f42573ce130dba3b54671bc0ce4c79a073f903eaa999daf806d6998 |
| docs/CANDIDATE-46-CERTIFICATE-TRANSCRIPT.json | 1854 | ffe941e89404d13294d44f017f96fb083667800a45ae545f0fea8e1270172388 | 1921 | 3179fe35dde321ba19f0ed7625124a7850a41a7b61ea7b58a64cf1b4af240ea0 |
| docs/CANDIDATE-46-KILLTEST-TRANSCRIPT.json | 1599 | b5472762dcc462d05fd70531dec74c7091e342102a01e4fb1092f618ab185e20 | 1662 | 1c3ac33db2c926e7e36f0bc827095c096a739895ec20ac012e8423bca703cf6b |

The raw text files were LF at capture time, so raw and LF hashes coincide.

The binary PDF is frozen separately:

| Path | Bytes | SHA-256 |
|---|---:|---|
| output/pdf/birkhoff_dobrushin_wall.pdf | 98044 | d3af8a9ce530ff97b1cf728917ff0c19deefa9b49b62685cbe7c8a9bfca826f7 |

### Paper-level attacks attempted

1. **Priority overclaim attack.** The sharp TV--Hilbert inequality was found in
   Cohen--Fausti, and Hopf-oscillation/Dobrushin identification in
   Gaubert--Qu. Both are now foregrounded as known; the candidate contribution
   was narrowed to equality iff plus tensor/global-local synthesis.
2. **Tensor kill test.** Exact enumeration through \(L=4\) confirmed
   \(\Theta(K^{\otimes L})=9^L\) and the degeneration
   \((3^L-1)/(3^L+1)\to1\), while the normalized product spectral ratio stays
   \(1/2\).
3. **Equality attack.** The certificate checks reciprocal two-block
   saturators and 1,495 finite binary pairs. A proposed two-atom strict chord
   example was rejected because two atoms automatically occupy both
   likelihood-ratio endpoints; a three-atom strict example was substituted.
4. **Optimization attack.** The harness was repeated under python -O and
   uses explicit exceptions, not removable assert statements.
5. **Global/local confusion attack.** The paper proves that the global
   Dobrushin coefficient also tends to one, while proving exact
   volume-independent contraction only for coordinate oscillations.
6. **Weight repair attack.** Positive left/right diagonal weights cancel in
   every cross ratio and therefore do not repair the global projective wall.
7. **Binary saturation attack.** The Ising link realizes
   \(\delta=\tau=\tanh|J|\), while its tensor Birkhoff coefficient is
   \(\tanh(L|J|)\).
8. **Transport-integrity attack.** Control-character scanning and full visual
   rendering caught defects invisible to compilation alone; the final scan
   passed.
9. **Formalization-status attack.** No source file is presented as a current
   .olean; no Lean, Lake, oracle, or Colab verification is claimed.
10. **Independent-review attack unavailable.** Fable was not run because the
    visible account violated the binding account instruction. This absence is
    a recorded limitation, not silently treated as review.

## Formalization supplement freeze (August 4, 2026)

Freeze status: **machine-checked algebraic core and revised paper; external
mathematical, novelty, and score verdict still required**.

This supplement responds to the external-review attack that assigned 4.86/10
and identified the absence of a current Lean artifact as a material weakness.
It supersedes the paper-level formalization-status paragraph and PDF above,
while preserving the earlier freeze as provenance.

- Branch: `codex/candidate-46-birkhoff-dobrushin-wall`
- Frozen body commit: `1b91f245c83b60d7d833c5fbb1448151ec19df71`
- Base `main`: `12bf6e241694aa5cfb5c7a6e08a96c8fa47ff9b1`
- Main divergence at freeze: branch ahead, `main` ahead by zero commits; no
  merge commit was required
- Capture host: Windows owner desktop, isolated worktree
- Capture method: `System.IO.File.ReadAllBytes`, UTF-8 decode, explicit LF and
  CRLF normalization, and `System.Security.Cryptography.SHA256.HashData`
- Local Lean/Lake/oracle: not invoked
- Remote runtime: Colab Pro+ CPU, high RAM (50.99 GiB visible), no GPU, account
  `lluiseriksson@gmail.com`
- Runtime opened: approximately `2026-08-04T19:36:00+02:00`
- Runtime closed: `2026-08-04T20:04:18+02:00`
- Close method: Colab UI “disconnect and delete runtime”; disconnected state
  verified after confirmation
- Lean: `leanprover/lean4:v4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`
- Notebook capture:
  `https://colab.research.google.com/drive/11N9BAjGa_w4ikrI9bAl9Jkx-5iYxpRzS`
- PDF compiler: Tectonic, final exit 0 in 8.3 s; only the host Fontconfig
  default-file diagnostic remained, with no TeX warnings
- PDF QA: 9 pages rendered; changed abstract and formalization/conclusion pages
  inspected after the final compile; temporary PNGs deleted and reproducible
- Arithmetic regression: normal and `python -O` runs both exit 0
- Fable/Claude: not invoked because the visible account remained
  `luis.ebikeride@gmail.com`, not the binding account
  `masterythief@gmail.com`
- External audit: not performed; no terminal score or priority verdict is
  claimed

### Frozen text and source bodies

| Path | Raw bytes | SHA-256 raw | LF bytes | SHA-256 LF | CRLF bytes | SHA-256 CRLF |
|---|---:|---|---:|---|---:|---|
| `YangMills.lean` | 264 | `0d6a40e97e745223356b97ed4ec4fa0925848b03245ea98d1a82d1bf056ffdbd` | 260 | `2ef46f1966e8746c7ecc007591344f8bc396e1f84169a599a8b8ff156d0fdfe1` | 266 | `e9bbfef0a5f3f63f11ac178d43f9a8d4bc3be685681391a9363a0367cb96a48f` |
| `YangMills/BirkhoffDobrushin/Wall.lean` | 9277 | `a477ca8b77133583b16f40f9a55ffab6da6296d873a62de7bebddd1571dca0e8` | 9277 | `a477ca8b77133583b16f40f9a55ffab6da6296d873a62de7bebddd1571dca0e8` | 9546 | `3fd48240bbbdca777bb0c7baaca5ccf60220978e56bc0a28d5dd50a42e7709d6` |
| `docs/CANDIDATE-46-BIRKHOFF-DOBRUSHIN-WALL.md` | 13304 | `650c5ae8bb45fd8efd5c1e1a0790146a202f7d3f11dcaef4d9abde85eb845fea` | 13304 | `650c5ae8bb45fd8efd5c1e1a0790146a202f7d3f11dcaef4d9abde85eb845fea` | 13629 | `1f25e811ac0732620e3dce9a5bcbd1069cdc4b5a345b44bbf3bb0a8f8c328681` |
| `docs/CANDIDATE-46-LEAN-VERIFICATION.json` | 4853 | `9d935ab1d70c96f1d1fbce0e72a880a91743c905ba2a5c809326c66c44599933` | 4853 | `9d935ab1d70c96f1d1fbce0e72a880a91743c905ba2a5c809326c66c44599933` | 4974 | `b1071930346df687ad733f49e6b3e3e9444ccd50d57684d0f7c8209412d5ccb1` |
| `papers/birkhoff-dobrushin-wall/birkhoff_dobrushin_wall.tex` | 27507 | `5ff076ff978e2e5f24d6aef20423eb19dc9cf2134845b9173f360ad1e5142605` | 27507 | `5ff076ff978e2e5f24d6aef20423eb19dc9cf2134845b9173f360ad1e5142605` | 28172 | `5c00e938a68cd33524db86f25bfe589aafbaeb99069eaa5cfd031b41cba8a6c3` |
| `scripts/certify_birkhoff_dobrushin_comparison.py` | 5803 | `4d677c431d63721710e15b39bd1472149c5e9487b0b6d7010d8963be782fdbde` | 5803 | `4d677c431d63721710e15b39bd1472149c5e9487b0b6d7010d8963be782fdbde` | 5981 | `a35806ca0eeee6c480f88104fcba4827e0f1490b6495bdf74796289a88970afa` |
| `scripts/killtest_birkhoff_tensor_wall.py` | 2679 | `b0bd9f744331acdf769b194d922e75bcff7f64d15709904584cfe85526729412` | 2679 | `b0bd9f744331acdf769b194d922e75bcff7f64d15709904584cfe85526729412` | 2763 | `cebcb22f2da82be389dd62f7598bd9f679141612105484d9fadb0cb49aa146f9` |

The revised binary PDF is frozen separately:

| Path | Bytes | SHA-256 |
|---|---:|---|
| `output/pdf/birkhoff_dobrushin_wall.pdf` | 105847 | `b670a475354bded1a7c01530da95b2cabc97da88d6acbf51da19b88c9872cb52` |

### Formalization attacks attempted

1. **Pinned-library attack.** The first compile failed because
   `Real.tanh_add` was unavailable in the pinned Mathlib. The proof was
   reformulated as the equivalent rational hyperbolic-addition identity.
2. **Stale-olean attack.** A later failed compile left the previous `.olean`
   on disk. The transcript marks it stale, deletes it before the successful
   pass, and never counts source presence or stale output as verification.
3. **Equality-rigidity attack.** Endpoint rigidity is checked both pointwise
   and for strictly positive finite weighted sums.
4. **Local-step attack.** A wrongly oriented sum rewrite failed compilation;
   the corrected `calc` proof was recompiled from a source whose hash matches
   the local file byte for byte.
5. **Notebook-transport attack.** A malformed Python patch cell failed before
   invoking Lean and remains in the transcript as a failed pass.
6. **Package-search-path attack.** A nested module compiled, but a separate
   import correctly failed while the `.olean` was outside
   `.lake/build/lib/lean`. The final pass materialized it in the package search
   path and separately compiled three imported `#check` declarations.
7. **Final import result.** Module exit 0, separate-import exit 0, module
   `.olean` SHA-256
   `1283835e606faa1797d86d47ea01b23e1aa1baf378a9c3d559642f6c60026490`.
8. **Scope-inflation attack.** The paper and transcript explicitly leave the
   general analytic Birkhoff--Hopf theorem, logarithmic diameter passage,
   probability-normalized end-to-end kernel theorem, Hellinger product proof,
   and interacting Dobrushin theorem as external inputs.
9. **No-false-gap attack.** The Lean module formalizes the calculation and
   wall; it does not assert a volume-uniform global projective gap.
10. **Runtime-governance attack.** Lean/Lake stayed off Windows; Colab used CPU
    high RAM without GPU and was disconnected and deleted at completion.
