# D-7 release manifest

This is an evidence record for external audit, not a terminal certification.

## Frozen objects

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

