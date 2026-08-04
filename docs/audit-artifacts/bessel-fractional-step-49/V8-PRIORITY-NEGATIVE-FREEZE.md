# V8 priority-negative body freeze — audit 49

This manifest freezes the priority-corrected body offered to a later
independent reviewer. It does not certify its own mathematics, bibliography,
or publication grade.

## Git identity

- Branch: `codex/audit-bessel-fractional-49`
- Frozen body commit: `699dab6668d212489ff56c776aaa74f9b32632d9`
- Frozen body tree: `d69064e386ad24a3830ff25bb0becb99bb2c694e`
- Parent: `04df247ff6d8ced1f6fd6536d731665dea0aa358`
- Capture time: `2026-08-04T21:14:16.9777956+02:00`
- `origin/main` at capture: `04f87347f3e4d46a05e77bc1c70855794e111477`
- `git merge --no-edit origin/main`: `Already up to date`

The manifest itself is committed after the body so the referenced tree is
immutable and self-reference is avoided.

## Capture method

Raw hashes are SHA-256 over exact worktree bytes at the body commit. For text
files, the LF capture decodes as UTF-8, maps CRLF and bare CR to LF, and
re-encodes as UTF-8 without BOM. The CRLF capture maps every LF in that stream
to CRLF. Git blob IDs are resolved from the frozen body commit.

| File | Raw bytes | Raw SHA-256 | LF bytes | LF SHA-256 | CRLF bytes | CRLF SHA-256 | Git blob |
|---|---:|---|---:|---|---:|---|---|
| `AmosClosure/BesselNegative.lean` | 10964 | `4b3d3d250f9798942733d30b1c87a7a4994da33f80c39460554141268ee9b525` | 10964 | `4b3d3d250f9798942733d30b1c87a7a4994da33f80c39460554141268ee9b525` | 11227 | `111ebd65eae1b6116e4b3ce86a155d7713bbb743ecb88fc8a9b82c2eb06f127f` | `a87ea5cfa2e21883c5dafd6a8a87fc67e98641fc` |
| `AmosClosure/FractionalOrderOptimal.lean` | 30813 | `db426c9b3619b12d0e58a5752915c06bdd48b7f6cac41c0d976dbebfbabb50f6` | 30813 | `db426c9b3619b12d0e58a5752915c06bdd48b7f6cac41c0d976dbebfbabb50f6` | 31514 | `c96087e4fcc8a852982207ac0ba9afab1f7be4980bf594722711df9b7fd1cb61` | `4b8d28e5047f31b24efccad9faeb493240a65bcc` |
| `AmosClosure.lean` | 1008 | `d30ec6e09e800c00039e0f3bcf735aec3134480bc614ad69d7233e4ce66554c1` | 981 | `ce8679314887457f90f5ee246e7fb57dcc731e40695238da083adfc3dd3f43e4` | 1012 | `ba7b25b13e1b6f3260d977f68941a9c88f13ffeb19ce29bd840a236843240a08` | `5bd5ccafdc3f95c88edb252e3b7b8a5c6ea48570` |
| `AmosClosure/Oracle.lean` | 11030 | `8291b43e6505208a7488262981689b116969d3c84c1071929af8d0249c615534` | 10824 | `c6a25170312103d018218cdd1d10ef5d6bf1e67fa72497146f358c7ed2039067` | 11059 | `1763c1282cfcc5343eec6b1038d97e53b396134fc1f0e1f3bd9f9302651f086b` | `1c4efd54a553d06a071822e4938b466fa0f2e0a3` |
| `docs/BESSEL-FRACTIONAL-STEP-AUDIT-20260804.md` | 11559 | `618642c7b91fbbee64182d07151cbdcadcdf0cf46c500188aef9bafe02b2a7f3` | 11559 | `618642c7b91fbbee64182d07151cbdcadcdf0cf46c500188aef9bafe02b2a7f3` | 11845 | `1a2f661d3a75ec0e68390ed00888e0113337dccbcb0e351f8e44a8ef43740958` | `8c1dfdb651269d6298a40d7681cfd341a9379dc2` |
| `docs/audit-artifacts/bessel-fractional-step-49/COLAB-LEAN-VERIFICATION.md` | 1892 | `dd494ce64294cf50ff81e049ec33a9e918ea2e82ad86034239fbc76a0f4ba537` | 1892 | `dd494ce64294cf50ff81e049ec33a9e918ea2e82ad86034239fbc76a0f4ba537` | 1939 | `7357fa998cf3edbd44b5e71ffc2f4885f9c0f6cd64ad06ebfe2da38558c61973` | `3a08ab7fd62d163bea21dbc70ed6e444b55d0cd1` |
| `papers/bessel-amos-fh/LEAN-VERIFICATION-LOG.txt` | 1017 | `9fa6f042d79c9e596eb066ffce3d7f914f451d57b9f29424b0d073bc188ee154` | 1017 | `9fa6f042d79c9e596eb066ffce3d7f914f451d57b9f29424b0d073bc188ee154` | 1045 | `9ab4c5927ec9f4c6d0cbacc0b3e755768c79dc9ac0c6664bc1dbcf1ae354182c` | `cedf03f8f2cf1847a91709ca8e7a0b5a52efe0f7` |
| `papers/bessel-amos-fh/README.md` | 2447 | `988e41439ab8e1a0de407a85ef86eb642cffac95058df8d7bbcbe59e9ccfd358` | 2447 | `988e41439ab8e1a0de407a85ef86eb642cffac95058df8d7bbcbe59e9ccfd358` | 2491 | `3153c5c57f437825d87d41327ad09a869359ff32e26c3414f876367f43970856` | `fe0438a38dec981709288151c8d45a1ef351dee0` |
| `papers/bessel-amos-fh/bessel_amos_fh.tex` | 32163 | `19aa9aa32ae7b9369d4aaae755923ceb10b99c8f1bcb760091f9dcc31c8d88f7` | 31818 | `2eb11925a39690fc6f0981a35f88b4515eb40a1426a128fafaa15a9aaa4d4ece` | 32607 | `592d5eff54af81925d4a671ca48ae149169bb23349c8722558353d67f1bfc200` | `eca76e2ae65f7a5462d9c202f4d7a5bba9cbfe36` |
| `scripts/audit49_fractional_bessel.py` | 3727 | `9bee93e063db99feede5e28ab81868f41cafe5405cfcac700d6e8dd1c63f1304` | 3727 | `9bee93e063db99feede5e28ab81868f41cafe5405cfcac700d6e8dd1c63f1304` | 3843 | `226c16853d346c3bb8f737be5a671d48c342e9fa9e0800f4912d05d8f7250087` | `e6d0595d92ce43b8893c23706fa5905aee8e0930` |

Binary artifacts:

| File | Raw bytes | Raw SHA-256 | Git blob |
|---|---:|---|---|
| `papers/bessel-amos-fh/bessel_amos_fh.pdf` | 374336 | `93a32ec29889412a96eb3ed9e16377601a2065dbc6a642ff772fb2feeab20208` | `bcc184d836e192192bbb27fd48270e0009ae17c7` |
| `output/pdf/bessel_fractional_order_v8.pdf` | 374336 | `93a32ec29889412a96eb3ed9e16377601a2065dbc6a642ff772fb2feeab20208` | `bcc184d836e192192bbb27fd48270e0009ae17c7` |

## Priority witness and disposition

- Literal unrestricted inequality: **FAIL**, with the previously frozen
  witness `(mu,nu,x)=(-0.8,-0.4,10)`.
- Adjusted optimal-domain theorem: mathematically retained and already
  machine checked.
- Fabrication as a new analytic theorem of grade `+6`: **FAIL**.
- Garofalo, Proposition 8.8, gives the exact classical unit-shift threshold
  `nu >= -1/2`: <https://arxiv.org/abs/1810.09756>.
- Garofalo points to Yuan--Kalbfleisch (2000), Appendix:
  <https://www.ism.ac.jp/editsec/aism/52/438.html>.
- The arbitrary-shift iff is a short corollary of Freitas--Laugesen Lemma 10,
  DLMF 10.27.2 and 10.28.2, and DLMF 10.40.1--10.40.4:
  <https://arxiv.org/abs/1810.07461>, <https://dlmf.nist.gov/10.27>,
  <https://dlmf.nist.gov/10.28>, <https://dlmf.nist.gov/10.40>.
- Hartman 1976, Theorem 1.0, is an older structural antecedent in the order
  square: <https://www.numdam.org/item/ASNSP_1976_4_3_2_267_0/>; its erratum
  is <https://www.numdam.org/item/ASNSP_1976_4_3_4_725_0/>.
- Defensible residual contribution: explicit synthesis, recurrence-only
  Riccati proof without `K` or asymptotics, and complete Lean formalization.

## Checks on this revision

- No Lean source changed after the recorded Colab materialization, so no new
  Lean/Colab run was made and no local Lean/Lake process was started.
- The TeX source compiled in two clean local-light `pdflatex` passes.
- Final log search found no warnings, undefined references, overfull boxes,
  or underfull boxes.
- The 11 final pages were rendered at 120 dpi and visually inspected; no
  clipping, overlap, broken glyph, or illegible reference was found.
- PDF: 374336 bytes, 11 pages, SHA-256
  `93a32ec29889412a96eb3ed9e16377601a2065dbc6a642ff772fb2feeab20208`.
- No Claude Code, Opus 5, Fable 5, or Colab session was opened in this
  priority revision.

