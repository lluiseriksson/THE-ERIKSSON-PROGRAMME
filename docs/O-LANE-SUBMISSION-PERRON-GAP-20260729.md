# O-lane Paper 8 submission record (2026-07-29)

**State:** submitted, as reported by the owner.  The public ai.viXra
identifier had not yet been assigned when this record was written; it remains
`pending` until the public catalog supplies it.

## Frozen artifact

- Title: *Strict but Not Uniform: a Machine-Checked Spectral Gap at Every
  Finite Extent of the Coupled Slice*.
- Author: Lluis Eriksson.
- Category: Mathematics - Functional Analysis.
- Submission edition: v1.2, 6 pages.
- Paper commit: `b03766bde54dca1d30c2febea8c008483d53751e`.
- Formal Lean anchor: `ac8979631c1541b059b3c10f590ca174b0b5f6be`.
- Terminal endpoint:
  [`coupled_gap_all_eigenvalues`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/ac8979631c1541b059b3c10f590ca174b0b5f6be/YangMills/OS/PerronGap.lean#L483).
- PDF: [`papers/perron-gap/perron_gap.pdf`](../papers/perron-gap/perron_gap.pdf),
  83,708 bytes.
- PDF SHA-256:
  `e8063013965ea1699718d08f2bce1646e73f0dd2b970a518bb9e6339c68d78a0`.
- TeX SHA-256:
  `b8d8f14470d8df16ad08e2bd52ef94b9a992c55e15afec62eddb03ec2f89cd2b`.
- Exact submitted fields:
  [`SUBMISSION-INFO.txt`](../papers/perron-gap/SUBMISSION-INFO.txt).

The PDF at the owner's submission path
`C:\Users\lluis\Desktop\YangMills\ENVIAR-AHORA\perron_gap.pdf` was compared
byte-for-byte with the repository PDF on 2026-07-29 and was identical.  The
hashes and byte counts above were recomputed locally after synchronizing with
public `main`.

## Machine-checked boundary

The terminal theorem covers every complex eigenvalue of the finite coupled
kernel: for every finite extent, every beta, and every strictly positive
source weight, every eigenvalue distinct from the Perron eigenvalue has
strictly smaller modulus.  The paper also packages the normalized vacuum.

The result is strict but not quantitative.  It supplies no separation modulus,
no bound uniform in the extent, and no proof that a volume-uniform bound is
impossible.  The reported ratios at extents 2 through 5 are measurements, not
theorems, and no theorem depends on them.  Nothing here concerns `SU(N)`, a
continuum limit, or the Yang--Mills mass gap.

## Verification checkpoint

- `lake build YangMillsCore`: 8428 jobs, success.
- Oracle: 2583 commands and 2583 answers; 2560 with axiom dependencies and 23
  axiom-free.
- Axiom set: exactly `{propext, Quot.sound, Classical.choice}`.
- Zero `sorryAx`, zero project axioms, zero errors.

No public identifier is inferred from submission order or a nearby archive
number.  This record moves to the public table only after the title appears in
the public catalog and its public PDF has been compared with this frozen
artifact.
