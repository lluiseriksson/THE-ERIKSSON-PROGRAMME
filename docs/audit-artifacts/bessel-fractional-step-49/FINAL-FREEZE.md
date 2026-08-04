# Final body freeze — audit 49 and paper v7 optimal-domain completion

This manifest freezes the implementation-and-paper body offered for a later
independent terminal review. It does not certify its own mathematics,
priority, or publication grade.

## Git identity

- Branch: `codex/audit-bessel-fractional-49`
- Frozen body commit: `1929f8d04994607347352d68f24d01980cdb4595`
- Frozen body tree: `6d575645f51befce3422195ec04fb703861f6a9b`
- Parent: `9e0e43be983db79df4a35e0a7a1e5066e5e096f7`
- Capture time: `2026-08-04T20:44:46+02:00`
- `origin/main` at capture: `04f87347f3e4d46a05e77bc1c70855794e111477`;
  `git merge --no-edit origin/main` reported `Already up to date`

The manifest itself is committed after the body so that the referenced tree
is immutable and self-reference is avoided.

## Capture method

Raw hashes are SHA-256 over exact worktree bytes at the body commit. For text
files, the LF capture decodes as UTF-8, maps CRLF and bare CR to LF, and
re-encodes as UTF-8 without BOM. The CRLF capture maps each LF in that stream
to CRLF. Git blob IDs are resolved from the frozen commit.

| File | Raw bytes | Raw SHA-256 | LF bytes | LF SHA-256 | CRLF bytes | CRLF SHA-256 | Git blob |
|---|---:|---|---:|---|---:|---|---|
| `AmosClosure/BesselNegative.lean` | 10964 | `4b3d3d250f9798942733d30b1c87a7a4994da33f80c39460554141268ee9b525` | 10964 | `4b3d3d250f9798942733d30b1c87a7a4994da33f80c39460554141268ee9b525` | 11227 | `111ebd65eae1b6116e4b3ce86a155d7713bbb743ecb88fc8a9b82c2eb06f127f` | `a87ea5cfa2e21883c5dafd6a8a87fc67e98641fc` |
| `AmosClosure/FractionalOrderOptimal.lean` | 30813 | `db426c9b3619b12d0e58a5752915c06bdd48b7f6cac41c0d976dbebfbabb50f6` | 30813 | `db426c9b3619b12d0e58a5752915c06bdd48b7f6cac41c0d976dbebfbabb50f6` | 31514 | `c96087e4fcc8a852982207ac0ba9afab1f7be4980bf594722711df9b7fd1cb61` | `4b8d28e5047f31b24efccad9faeb493240a65bcc` |
| `AmosClosure.lean` | 1008 | `d30ec6e09e800c00039e0f3bcf735aec3134480bc614ad69d7233e4ce66554c1` | 981 | `ce8679314887457f90f5ee246e7fb57dcc731e40695238da083adfc3dd3f43e4` | 1012 | `ba7b25b13e1b6f3260d977f68941a9c88f13ffeb19ce29bd840a236843240a08` | `5bd5ccafdc3f95c88edb252e3b7b8a5c6ea48570` |
| `AmosClosure/Oracle.lean` | 11030 | `8291b43e6505208a7488262981689b116969d3c84c1071929af8d0249c615534` | 10824 | `c6a25170312103d018218cdd1d10ef5d6bf1e67fa72497146f358c7ed2039067` | 11059 | `1763c1282cfcc5343eec6b1038d97e53b396134fc1f0e1f3bd9f9302651f086b` | `1c4efd54a553d06a071822e4938b466fa0f2e0a3` |
| `docs/BESSEL-FRACTIONAL-STEP-AUDIT-20260804.md` | 8825 | `6c6692808b2d259c804ab218586d2b3a4c836a9b9c85f512de5207b5814ce19d` | 8825 | `6c6692808b2d259c804ab218586d2b3a4c836a9b9c85f512de5207b5814ce19d` | 9048 | `9d928101a757a366d6573f44822dfc812f5458176fd1cdb603b2c1d3d4c1be20` | `baa2ff3ad18d07583e88c8de569d721115da3765` |
| `docs/audit-artifacts/bessel-fractional-step-49/COLAB-LEAN-VERIFICATION.md` | 1892 | `dd494ce64294cf50ff81e049ec33a9e918ea2e82ad86034239fbc76a0f4ba537` | 1892 | `dd494ce64294cf50ff81e049ec33a9e918ea2e82ad86034239fbc76a0f4ba537` | 1939 | `7357fa998cf3edbd44b5e71ffc2f4885f9c0f6cd64ad06ebfe2da38558c61973` | `3a08ab7fd62d163bea21dbc70ed6e444b55d0cd1` |
| `papers/bessel-amos-fh/LEAN-VERIFICATION-LOG.txt` | 1017 | `9fa6f042d79c9e596eb066ffce3d7f914f451d57b9f29424b0d073bc188ee154` | 1017 | `9fa6f042d79c9e596eb066ffce3d7f914f451d57b9f29424b0d073bc188ee154` | 1045 | `9ab4c5927ec9f4c6d0cbacc0b3e755768c79dc9ac0c6664bc1dbcf1ae354182c` | `cedf03f8f2cf1847a91709ca8e7a0b5a52efe0f7` |
| `papers/bessel-amos-fh/README.md` | 1949 | `897be1d85e6d92b302ba580298e0393118653addfb381f051fe31b1e6572605a` | 1949 | `897be1d85e6d92b302ba580298e0393118653addfb381f051fe31b1e6572605a` | 1986 | `68161a54e726bbd5492c3eb4610bdb846f63038e3048514400353122738f39a4` | `1c444aa7a4d1571dfa218f73a4ac400698fac13f` |
| `papers/bessel-amos-fh/bessel_amos_fh.tex` | 28381 | `3902c40df8406b1b5e6753f1e0b39ae31bdc4aeec0107e753af6c09df2aa58fa` | 28036 | `2b565539c61ece0ac754561e771239aa2e17edb35b0dc775502bd7198afdcb8e` | 28735 | `385d492f9a9b3b861811cff29b0623d778157f6a4058ac9857fde1f0885225f1` | `b619b3ad968a0a3111382c5baeb2badcb59642e7` |
| `scripts/audit49_fractional_bessel.py` | 3727 | `9bee93e063db99feede5e28ab81868f41cafe5405cfcac700d6e8dd1c63f1304` | 3727 | `9bee93e063db99feede5e28ab81868f41cafe5405cfcac700d6e8dd1c63f1304` | 3843 | `226c16853d346c3bb8f737be5a671d48c342e9fa9e0800f4912d05d8f7250087` | `e6d0595d92ce43b8893c23706fa5905aee8e0930` |

Binary artifacts:

| File | Raw bytes | Raw SHA-256 | Git blob |
|---|---:|---|---|
| `papers/bessel-amos-fh/bessel_amos_fh.pdf` | 361652 | `6c9205d67211dd5ce0b4a912bcf7c126e1437026381e3bd4ff2647f63b693019` | `51900f43df1473428d5259303f08248d945e672e` |
| `output/pdf/bessel_fractional_order_v7.pdf` | 361652 | `6c9205d67211dd5ce0b4a912bcf7c126e1437026381e3bd4ff2647f63b693019` | `51900f43df1473428d5259303f08248d945e672e` |

## Checks and disposition offered to the external reviewer

- Literal unrestricted statement: **FAIL**. Witness
  `(mu,nu,x)=(-0.8,-0.4,10)` gives
  `rho_mu-rho_nu=0.042682961675102858...>0.04`.
- Adjusted statement: for `-1<mu<nu`, the lower inequality is always strict;
  the upper inequality holds for all `x>0` iff `mu+nu>=0`.
- Technical fabrication of the adjusted theorem: **PASS**. Novelty and final
  publication grade remain assigned to an independent reviewer.
- Priority: Freitas--Laugesen Lemma 10 already contains the nonnegative theorem
  and first-contact route. The negative optimal boundary is only a candidate
  contribution after the recorded primary-source sweep.
- Adversarial rerun: 800 seeded cases at 100 decimal digits passed, including
  negative valid orders and exact `mu+nu=0`; both invalid-domain witnesses
  were reproduced. Runtime: 0.894 s local-light.
- Remote Lean: `BesselNegative` 8163 jobs,
  `FractionalOrderOptimal` 8167 jobs, integrated `AmosClosure` 8178 jobs;
  all `.olean` targets materialized.
- Oracle: every new registration reported exactly
  `[propext, Classical.choice, Quot.sound]`.
- Colab: visible account `lluiseriksson@gmail.com`, CPU/high-memory, 31 minutes,
  disconnected and deleted; three other owner sessions untouched.
- PDF QA: two clean final `pdflatex` passes, 9 pages, no undefined references,
  warnings, overfull or underfull boxes; all pages rendered at 120 dpi and
  visually inspected after the final change.

Suggested independent attacks: rebuild from the pinned environment; inspect
the reverse-interval Gronwall proof at `mu+nu=0`; inspect the recurrence-only
large-`x` contradiction; replay the counterexamples at higher precision; and
redo the Freitas--Laugesen/Segura/Hornik--Grün/Mao--Tian priority sweep from
the cited primary sources.
