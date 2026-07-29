# O-lane Paper 6 submission record (2026-07-29)

**State:** submitted, as reported by the owner.  The public ai.viXra
identifier had not yet been assigned when this record was written; it must
remain `pending` until the public catalog supplies it.

**Public recheck:** on 2026-07-29 the author page ended at `[93]`,
`ai.viXra.org:2607.0078`, and did not yet list this title.  The five preceding
O-lane public PDFs were matched byte-for-byte to the repository; see
[`PUBLICATIONS.md`](PUBLICATIONS.md).  This paper keeps its pending state until
the public title and PDF can be checked the same way.

## Frozen artifact

- Title: *Blind to the Coupling: a Second Machine-Checked Obstruction at
  Spatial Extent*.
- Author: Lluis Eriksson.
- Category: Physics - Mathematical Physics.
- Submission edition: v1.2.1, 9 pages.
- Paper commit: `3d313d9291b53dc9c470051fddc721013fe9d9dd`.
- Formal Lean anchor: `a70426f4c8a0ed733b4eee94fb01b158bc81fd08`.
- PDF: [`papers/spatial-birkhoff/spatial_birkhoff.pdf`](../papers/spatial-birkhoff/spatial_birkhoff.pdf),
  118,268 bytes.
- PDF SHA-256:
  `42617528c0df0ad3e813ee77c11722c53e5ea1b4b97dc93f22d9ece45d29e4cb`.
- TeX SHA-256:
  `196a8cd8ff00747531a3eecc3318d8cb43ed7e825953384a4fa2f4c886c842a2`.
- Exact submitted fields:
  [`SUBMISSION-INFO.txt`](../papers/spatial-birkhoff/SUBMISSION-INFO.txt).

The hashes and byte count above were independently recomputed from the
published `main` tree before this record was committed.

## Claim boundary

The machine-checked contribution has three parts:

1. the Hilbert-projective cross-ratio is blind to the spatial coupling,
   including the two-sided/symmetrised convention;
2. the resulting diameter bound degenerates with spatial extent, while the
   decoupled exact ratio stays volume-independent;
3. at the smallest interacting size, an explicit strictly positive
   eigenvector is exhibited and its eigenvalue is proved to dominate every
   real or complex eigenvalue, hence is the spectral radius.

The paper does **not** prove a volume-uniform statement for an interacting
system, a general-`L` Perron--Frobenius theorem, uniqueness or simplicity of the
positive eigenvector, an `SU(N)` result, a continuum limit, or a Yang--Mills
mass gap.  The general-`L` interacting behaviour remains measured and unproved.

## Continuation

The next reusable formal target is the Hilbert metric/Birkhoff contraction
theorem and a general finite-dimensional Perron--Frobenius package in Lean.
That target is a recommendation, not a theorem or a scheduled claim.  A
volume-uniform interacting gap is meaningful only in an explicit
high-temperature/small-coupling region; the unrestricted target is false.
