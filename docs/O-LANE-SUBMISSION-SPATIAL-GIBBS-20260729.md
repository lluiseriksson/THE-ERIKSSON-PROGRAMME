# O-lane Paper 9 submission record (2026-07-29)

**State:** submitted, as reported by the owner.  The public ai.viXra
identifier had not yet appeared when this record was written; it remains
`pending` until the public catalog supplies it.

## Frozen artifact

- Title: *The Measure the Spectral Results Were About: a Machine-Checked
  Transfer Bridge for the Spatial Z_2 Slice*.
- Author: Lluis Eriksson.
- Category: Mathematics - Functional Analysis.
- Submission edition: v1.1, 6 pages.
- Paper commit: `dc2935eb7f4b299aada889c39a119d415b533951`.
- Formal Lean anchor: `c4fa6a9e6769496a7270981ef0908b2d644c230b`.
- Normalised-expectation endpoint:
  [`gibbsCorr_eq_ratio_iterate`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/c4fa6a9e6769496a7270981ef0908b2d644c230b/YangMills/OS/SpatialGibbs.lean#L277).
- Positive-denominator endpoint:
  [`gibbsCorr_denom_pos`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/c4fa6a9e6769496a7270981ef0908b2d644c230b/YangMills/OS/SpatialGibbs.lean#L288).
- PDF:
  [`papers/spatial-gibbs/spatial_gibbs.pdf`](../papers/spatial-gibbs/spatial_gibbs.pdf),
  86,847 bytes.
- PDF SHA-256:
  `92c8235c54c8c6cafa7325d1a126f8b962ea486ac9e95d2e0872ec25969ce243`.
- TeX SHA-256:
  `abebc74cf56a2feec5efd157a5be6bd8e364516aa220b8df6f7f3b05b2fb0bbe`.
- Exact submitted fields:
  [`SUBMISSION-INFO.txt`](../papers/spatial-gibbs/SUBMISSION-INFO.txt).

The PDF at the owner's submission path
`C:\Users\lluis\Desktop\YangMills\ENVIAR-AHORA\spatial_gibbs.pdf` was compared
byte-for-byte with the repository PDF on 2026-07-29 and was identical.  The
hashes and byte counts above were recomputed locally after synchronizing with
public `main`.

## Machine-checked boundary

The paper defines the finite two-dimensional Gibbs weight of the spatial
`Z_2` slice and proves its exact boundary dressing by the path weight of the
symmetrised kernel.  It identifies the unnormalised Gibbs two-point sum with
an iterated self-adjoint transfer-matrix element, then identifies the
normalised expectation as the ratio of two such elements and proves the
denominator strictly positive.  It also proves fluctuation-sector invariance
and geometric connected decay under an explicit contraction hypothesis.

That contraction hypothesis is carried, not discharged.  The preceding
strict finite-spectrum gap supplies no quantitative operator-norm modulus by
itself, and this paper constructs no spectral maximum on the fluctuation
sector.  Nothing is uniform in the spatial extent.  Reflection positivity is
not addressed, and there is no `SU(N)`, continuum, Yang--Mills mass-gap, or
Clay conclusion.

The brute-force recomputation for `L <= 3` and `N <= 3` is independently
verified numerical evidence about the definitions, not a theorem and not an
input to one.

## Verification checkpoint

- `lake build YangMillsCore`: 8429 jobs, success.
- Oracle: 2626 commands and 2626 answers; 2603 with axiom dependencies and 23
  axiom-free.
- Axiom set: exactly `{propext, Quot.sound, Classical.choice}`.
- Zero `sorryAx`, zero project axioms, zero errors.

The public author page was rechecked on 2026-07-29 and still ended at item
`[93]`, `ai.viXra.org:2607.0078`.  No identifier is inferred from submission
order or a nearby archive number.  This record moves to the public table only
after the title appears in the public catalog and its public PDF has been
compared with this frozen artifact.
