# D-7/D-9 release manifest

This is an evidence record for external audit, not a terminal certification.

## D-9 extension status -- FRESH COLAB PASS

The D-9 source is frozen in a dedicated commit.  Three targeted builds, the
full `YangMillsCore` integration, and the complete axiom oracle passed in a
fresh Colab Linux runtime.

- Branch: `codex/d9-dlr-cstar`
- Base D-8 release: `5cab0ba273f9b0d19abfb1ed8e64087919e4488c`
- D-9 Lean source anchor: `f587b35001f4ae87c7fe0383662864df6bc9a1c0`
- D-9 source tree: `ea4e4e9a2913275273efe98c09ca58c16ac7f3b7`
- Source delta: 6 files, 1,657 insertions
- New modules: `YangMills.OS.DobrushinUniformState`,
  `YangMills.OS.DobrushinCStarState`, and
  `YangMills.OS.DobrushinFiniteSetDLR`
- Lean: `v4.29.0-rc6`
- Observed fresh-runtime cost: approximately 72 minutes for `YangMillsCore`
  and 45 minutes for `oracle_check.lean`, excluding the targeted builds
- Source transport: exact local D-9 files were copied into a fresh Colab
  Linux project/runtime.  This is fresh-platform compilation evidence, not an
  independent public-clone replay of the still-unpublished source commit.

Fresh Colab targeted validation:

```text
lake build YangMills.OS.DobrushinUniformState
exit 0; Build completed successfully (8178 jobs)

lake build YangMills.OS.DobrushinCStarState
exit 0; Build completed successfully (8179 jobs)

lake build YangMills.OS.DobrushinFiniteSetDLR
exit 0; Build completed successfully (8180 jobs)

lake build YangMillsCore
exit 0; Build completed successfully (8494 jobs)
2,120 lines; 135,769 bytes
log SHA-256 8aaffa8ec2d7c7e037302824c327e205a9f46b6c7fd3f257704574b8d4a9971e

lake env lean oracle_check.lean
exit 0; 5,481 lines; 369,750 bytes
log SHA-256 f2f06a6f844ff936bdc12310d959a0251dfbb7e411b1f5758360938f6593b5b9
```

All 19 D-9 declarations listed by the final oracle block were present.  Their
reported dependencies are subsets of
`[propext, Classical.choice, Quot.sound]`; notably,
`finiteSetSwap_involutive` reports only `[propext, Quot.sound]`, while the
terminal `expect_finiteSetCondExp` reports exactly
`[propext, Classical.choice, Quot.sound]`.

The algebraic result constructs the intrinsic uniform norm on the real local
cylinder quotient, its explicit complex star algebra and faithful bounded
continuous-function representation, the concrete commutative C-star closure,
a dense local embedding, and a positive norm-one continuous extension
`quasilocalCStarState`.  The finite-geometry result constructs normalized
positive Gibbs kernels for arbitrary finite subsets of a finite ambient type,
their conditional expectations, exterior locality, idempotence, and the exact
finite-volume Gibbs tower/fixed-point identity by an involutive reindexing.

The following claims remain deliberately out of scope: the infinite-volume
DLR fixed-point identity for the completed state; covariance of that completed
C-star state under the full `Z^2` action; arbitrary Folner/exhaustion
independence; nested finite-set specification consistency; a parameter region
beyond classical Dobrushin uniqueness; and any Yang--Mills consequence.  In
particular, the anisotropic Dobrushin envelope is sharper than a square window
but is not described as a non-classical region.

D-9 source corpus:

| File | Bytes | SHA-256 | LF | CR |
|---|---:|---|---:|---:|
| `YangMills/OS/DobrushinUniformState.lean` | 11,918 | `7de826a36be867ba9c67ec73710bfbc7b309873c6821c67cbd9d03afa34b6e26` | 312 | 0 |
| `YangMills/OS/DobrushinCStarState.lean` | 38,513 | `c42c9430cca4137626b4ee4915cf224596fcf84bccba288e3bed285fc9bc5dcf` | 881 | 0 |
| `YangMills/OS/DobrushinFiniteSetDLR.lean` | 11,467 | `23addb21e08f8195e113f98f31286d199cc8d20cfbfb455eef71b00a1280c94f` | 284 | 0 |
| `YangMillsCore.lean` | 65,991 | `32ae69630fb2b15006d0afae817e8082ba5ed6f4d1ec858222dd4bce73ddc7ba` | 1,077 | 1,060 |
| `oracle_check.lean` | 242,649 | `35f97ce1f2ffd1600ca9be602b70f3d724f77f22f2cef90be9bcd0a7ed5cf901` | 3,453 | 3,412 |
| `docs/D9-DLR-CSTAR-PLAN.md` | 6,623 | `bed0e1895b1c0938f0f76055d011123864cc01347fe875621772569205d3d740` | 141 | 0 |

Paper artifact after the verified render:

| File | Bytes | SHA-256 | LF | CR |
|---|---:|---|---:|---:|
| `papers/dobrushin-thermodynamic-limit/dobrushin_thermodynamic_limit.tex` | 49,756 | `2965e1351059815dc3ecb324b7372c7242c7c8ea7256617ccb1ac2b5c939816b` | 1,163 | 729 |
| `papers/dobrushin-thermodynamic-limit/README.md` | 1,207 | `0abf895f26b09b5ac808c0c519304485dbe93594ca1bbb2de664125abf55651a` | 22 | 7 |
| `output/pdf/dobrushin_thermodynamic_limit.pdf` | 377,505 | `7faecbb1a2799a00b93da255597030e2561104a98d01abe1c3b455e2661f8993` | n/a | n/a |

The PDF was produced with two final `pdflatex` passes, both exit 0.  It has 17
letter-size pages, correct title/author metadata, extractable text, no
encryption, no overfull boxes or undefined references, and every page was
rendered at 110 dpi and visually inspected.  The only remaining log diagnostic
is a visually harmless longtable page-break glue warning.

The remainder of this file preserves the D-8 and D-7 evidence records.  Their
counts and hashes apply only to the frozen objects named in those sections.

## D-8 extension status -- FRESH COLAB PASS

The D-8 extension has a frozen public Lean source commit, complete local
validation, and an independent replay from a newly created Colab runtime.
The notebook remained saved after the runtime was disconnected and deleted.
The paper/PDF artifact commit is recorded by the manifest-only seal commit
immediately following it.

- Branch: `codex/d7-covariant-cstar`
- Base D-7 release: `daa1b40d940d1f1b2a07de303271b37b6e736121`
- D-8 Lean source anchor: `6ce506bb6ad627e793485631a12f1271423f2bd4`
- D-8 source tree: `a65af9a2c13a290948cf5ba2a8b6500cc5097172`
- Paper/PDF artifact commit: `f49c4241d816174e13921cc7fca238a664d3819d`
- Source delta: 5 files, 1,282 insertions
- New terminal module: `YangMills.OS.DobrushinCovariantState`
- Analytic window: `0 <= alpha < 1` and
  `2*tanh|beta| + 2*tanh|gamma| <= alpha`; no KP premise

Local Windows validation on Lean `v4.29.0-rc6`:

```text
lake build YangMills.OS.DobrushinPeriodicTranslation
exit 0; Build completed successfully (8176 jobs)

lake build YangMills.OS.DobrushinCovariantState
exit 0; Build completed successfully (8177 jobs)

lake build YangMillsCore
exit 0; 160.8 s; Build completed successfully (8491 jobs)

lake env lean oracle_check.lean
exit 0; 1422.2 s; 5436 output lines
```

The eight new D-8 `#print axioms` declarations report exactly
`[propext, Classical.choice, Quot.sound]`.  A textual scan of the three new
modules finds no `sorry`, `admit`, or declared `axiom`.

The failed first integration attempt is retained as negative evidence: it
reached 8,488/8,491 targets in 2,485.3 s and exposed one missing simplifier
fact in `DobrushinPeriodicTranslation`; after the localized correction, both
the targeted and full builds above passed.

Fresh Colab replay:

- Notebook:
  <https://colab.research.google.com/drive/1gq7M8iuzK5RP-7-9jk2d4NQs3QfWBZWX>
- Visible Google account: `lluiseriksson@gmail.com`
- Runtime: newly created Colab CPU runtime, 12.67 GB RAM, no GPU requested
- Source transport: public clone of branch `codex/d7-covariant-cstar`, then
  detached checkout of the exact source anchor above
- Open marker: `2026-08-05T09:42:34Z`
- Close marker: `2026-08-05T11:47:31Z`
- Runtime disconnected and deleted: `2026-08-05T11:48:47.1538011Z`
- Lean: `v4.29.0-rc6`, commit
  `00659f8e6071d7e46131ed643bf8003b99b044e9`
- Lake: `5.0.0-src+00659f8`

```text
lake exe cache get
exit 0; 273 s; 47 lines; 30,701 bytes
log SHA-256 533cfff2c1d3f67fd15f93c7bc9f528ca321292fff57f1670a3cde0c94604e03

lake build YangMills.OS.DobrushinPeriodicTranslation
exit 0; 299 s; Build completed successfully (8176 jobs)
log SHA-256 2193912bb38b7fab45202fa3bc281824f8313a050a71a8abe5b247481813770e

lake build YangMills.OS.DobrushinCovariantState
exit 0; 47 s; Build completed successfully (8177 jobs)
log SHA-256 c764449fc72712c762d0b03ea2fc8e7b54f105f920ba60ee358a86208034760d

lake build YangMillsCore
exit 0; 4175 s; Build completed successfully (8491 jobs)
log SHA-256 514d705ff616228d7b5b667e4c545ff34c560e50a0316f1734c0ce865dee312c

lake env lean oracle_check.lean
exit 0; 2684 s; 5436 lines; 367,253 bytes
log SHA-256 a06038e01038392e070870d36632cfb5088854deda8cf5d743454b850ca3ca94

D8_FRESH_VALIDATION_PASS
```

All eight D-8 declarations named in `oracle_check.lean` were present in the
fresh oracle output.  Each depends exactly on
`[propext, Classical.choice, Quot.sound]` after normalizing line wrapping.

The D-8 result supplies an intrinsic finite-site cylinder quotient, descended
pointwise operations, a genuine additive `Z^2` action, a positive normalized
real-linear value, and invariance under every integer translation.  It does
**not** supply a bundled complex star algebra, uniform norm, C-star
completion, DLR theorem for arbitrary shapes, or Yang--Mills consequence.

Local paper corpus after the verified render:

| File | Bytes | SHA-256 | LF | CRLF |
|---|---:|---|---:|---:|
| `docs/DOBRUSHIN-D7-DRAFT.md` | 6,736 | `aa3577ba3946ecd252630176880fd51e4bc5cbc9696220574ab58f554e4d978c` | 36 | 98 |
| `papers/dobrushin-thermodynamic-limit/dobrushin_thermodynamic_limit.tex` | 40,094 | `16810c6742da7b7be8edf583ad635fadb043d6aa6836e398c346382d3e7b05c7` | 229 | 736 |
| `papers/dobrushin-thermodynamic-limit/README.md` | 872 | `8834512dba8da0b42967f9c9d1d3cc6eb8dfba007e56072b89c577b89b131ff5` | 11 | 7 |
| `output/pdf/dobrushin_thermodynamic_limit.pdf` | 342,880 | `2248cfe16c0853b6f8fb7e1e03994285c06ce04547250463d0f3a8b98ebe9be6` | n/a | n/a |

The local PDF build used two final `pdflatex` passes, both exit 0.  The final
log contains no overfull boxes or undefined references.  The PDF has 14
letter-size pages, the intended title/author/subject metadata, extractable
text, no JavaScript or encryption, and every page was rendered at 110 dpi and
visually inspected.  An overflowing dependency-map row found in an earlier
render was split before the recorded PDF was produced.

The remainder of this file is the preserved historical D-7 evidence record.
Its old Colab counts and hashes apply only to the frozen D-7 objects named in
that section; they are not evidence for D-8.

## Historical D-7 frozen objects

- Branch: `codex/d7-dobrushin-transplant`
- Lean source anchor: `39cad01b1d2032dc15244e9af19ce6fbffa55a1f`
- Paper/PDF artifact commit: `0b29ebaf42d04ce898c58a088554149128e980d2`
- Colab notebook:
  <https://colab.research.google.com/drive/1AYYLJ0bwAMR3OaDIssbno3xQivjrl7uh>
- Capture method: the three files changed by the source anchor were read from
  the isolated worktree, gzip/base64 transported into the Colab checkout, and
  SHA-256 checked before any build. The final TeX source was transported by the
  same method; the resulting PDF was returned as base64 and checked locally.

## Source corpus

| File | Bytes | SHA-256 | LF | CRLF |
|---|---:|---|---:|---:|
| `YangMills/OS/DobrushinInfiniteState.lean` | 21,454 | `a307b5fefa4cd14be7335314dd19f85f743164f30f8f5686c162839a5e30de07` | 501 | 0 |
| `YangMillsCore.lean` | 65,064 | `e5fcf0ddae1f1a0cf8f01f8b745aa286a0a6b7f783d3e0f990be42da3baee67f` | 14 | 1,048 |
| `oracle_check.lean` | 239,796 | `9e3c6a9c5ffd32bc1be5429c7a4258d204baa75bcdc0975b41134496b86075ff` | 27 | 3,386 |

The three Colab SHA-256 values matched these values byte for byte before the
full build.

## Paper corpus

| File | Bytes | SHA-256 | LF | CRLF |
|---|---:|---|---:|---:|
| `docs/DOBRUSHIN-D7-DRAFT.md` | 5,853 | `e05252932819d7b10a3fd17cde1c595e7bda7226c02bd37c7c533d6539172ac3` | 121 | 0 |
| `papers/dobrushin-thermodynamic-limit/dobrushin_thermodynamic_limit.tex` | 33,397 | `7100b55306b9ed8b63c8bb145cecb60bd20624a7b6c2af4e4a8829b5891bf9e8` | 827 | 0 |
| `papers/dobrushin-thermodynamic-limit/README.md` | 485 | `20745308a5dbfe2563cb98b146d01d0b9cdd6b1450880bc9bbcbd3d58d3833b8` | 11 | 0 |
| `output/pdf/dobrushin_thermodynamic_limit.pdf` | 273,281 | `781391512c7ee60c2265c4fde854c77cccbdeabfbe71b2de2ed45d49ab683ab4` | n/a | n/a |

The PDF has 12 letter-size pages, metadata title/author/subject, extractable
text, and no JavaScript or encryption. Every final page was rendered at 110 dpi
and visually inspected. One overlapping audit table found in the first render
was corrected before the frozen PDF was produced.

## Colab validation

- Visible Google account: `lluiseriksson@gmail.com`
- Runtime: Colab Pro+ CPU, high RAM (50.99 GB), no GPU
- Open marker: `2026-08-04T20:43:04.758718+00:00`
- Close-preparation marker: `2026-08-04T22:23:45.439106+00:00`
- Runtime disconnected and deleted: `2026-08-04T22:24:45.6349681+00:00`
- Total open interval: `01:41:40.8762501`

Commands and results:

```text
lake exe cache get
exit 0; 139.72 s

lake build YangMills.OS.DobrushinInfiniteState
exit 0; final targeted rebuild 19.26 s
Build completed successfully (8174 jobs)

lake build YangMillsCore
exit 0; 1092.23 s
Build completed successfully (8488 jobs)

lake env lean oracle_check.lean
exit 0; 2300.23 s
output 366187 bytes; 5416 lines
all four selected new terminal declarations present

pdflatex -interaction=nonstopmode -halt-on-error \
  dobrushin_thermodynamic_limit.tex
two final passes: exit 0; 0.58 s and 0.55 s
```

The TeX runtime needed `texlive-latex-base`, `texlive-latex-recommended`, and
`texlive-fonts-recommended`; apt update took 6.68 s and package installation
40.84 s. These setup times are not counted as proof-checking times.

## Honest frontier

The frozen result constructs a compatible family of positive normalized
real-linear centred-cylinder functionals, proves cofinal/support/auxiliary
parameter independence, and proves receding-boundary stability including
free-periodic equality. It does **not** construct the full translated cylinder
carrier, a `Z^2` action with inverses on that carrier, the C-star completion, or
a Yang--Mills consequence. Those are explicitly outside the proved boundary.

