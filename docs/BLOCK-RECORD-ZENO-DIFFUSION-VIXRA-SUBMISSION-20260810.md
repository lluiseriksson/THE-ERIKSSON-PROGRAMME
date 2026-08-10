# Block-record Zeno diffusion paper — ai.viXra submission record

Date recorded: **2026-08-10**

Current owner-reported operation: **v1 cancelled before publication; v3 sent
as the only live submission**

Moderation/publication outcome and public identifier: **not recorded here**

## Lifecycle resolution

The earlier record described an 11-page v1 object as submitted. The owner has
since clarified that this operation was cancelled without incident before it
became a public ai.viXra version. It is therefore classified as
**CANCELLED / NOT PUBLIC / NOT A VERSION OF RECORD**.

The 13-page v3 object below was then uploaded and sent. It is the only current
submission represented by this acta. The bundled v3 submission sheet still
contains replacement-form instructions written under the earlier assumption
that v1 would remain live; those operational instructions are superseded by
the owner's actual cancellation-and-new-upload sequence. The mathematical
title, abstract, comments and keywords in that sheet remain the v3 form
metadata.

The cancelled v1 artifact identity is retained at the end of this record for
internal traceability. Retaining it does not treat v1 as published, assigned an
identifier, or part of the public version history.

## Current paper identity — v3

Full submission title:

*Noncommuting Block Measurements Generate Quantum Diffusion: A
Three-Obstruction Convergence Hierarchy, a Noncommutative Connectivity Gap,
and Exact Algebraic Architectures*

- Author displayed on the first page: **Lluis Eriksson**
- Primary category: **Quantum Physics**
- Suggested secondary category: **Mathematical Physics**
- Language: **English**
- Version date: **10 August 2026**

The embedded PDF title remains the shorter *Noncommuting Block Measurements
Generate Quantum Diffusion*. Its embedded `/Author` field is empty even though
the first page visibly names `Lluis Eriksson`. This discrepancy is recorded
rather than silently normalized.

## Exact v3 submitted artifact

- Filename: `Noncommuting_Block_Measurements_Generate_Quantum_Diffusion_Definitive_v3.pdf`
- Pages: **13**
- Figures: **2**
- Bytes: **460,394**
- SHA-256: `1EBD2390B9BE9257E6D6772DEA56B6ACB90867674AA77C05CC53C5B3956A178F`

The PDF was rendered page by page. No clipping, overlap, broken glyph,
unreadable formula, table failure or figure-composition defect was observed.

Reproducibility package:

- Filename: `Noncommuting_Block_Measurements_Definitive_v3_Reproducibility.zip`
- Bytes: **461,980**
- SHA-256: `288F642B00D055ED1308364B4B0D2C4235CBF7B80993B9CB5E0F939CA97EB0C4`
- ZIP entries: **17**
- Manifest checks: **16/16 PASS**
- Embedded v3 PDF: **byte-identical** to the submitted artifact

No public PDF locator, source repository or Git commit was supplied for v3.
The dashboard therefore records null source anchors rather than fabricating
provenance.

## Exact v3 form metadata

Comments:

> 13 pages, 2 figures. This version supersedes v1/v2. It adds the exact
> quintic product obstruction P_H, a third injective Duhamel coefficient R_t,
> the sharp Theta(n^-3/2) branch, an O(n^-2) fourth level, and an exact
> algebraic three-record architecture proving that the new branch is attained.
> AI assistance is disclosed in the manuscript.

Keywords:

> quantum Zeno effect; nonselective measurement; quantum Markov semigroup;
> diamond norm; conditional expectation; product formula; higher-order
> asymptotics; irreducibility; spectral gap; GKLS generator; noncommuting
> projections

Abstract:

> Repeated projective measurements are usually discussed either in the
> ballistic Zeno scaling or after reduction to classical outcome probabilities.
> We study a different regime in which each nonselective measurement retains a
> full matrix algebra inside every degenerate outcome block. Let E(X)=sum_a P_a
> X P_a, let E_tau be its rotation by exp(-i tau H), and close one cycle by
> Phi_tau=E E_tau E. We prove, uniformly on compact time intervals and in
> diamond norm, that Phi_{sqrt(t/n)}^n converges to exp(-tK)E, where K=E
> ad_H(1-E)ad_H E=C_H^* C_H. The limit is a genuinely quantum Markov semigroup
> on the direct sum of the block matrix algebras, with explicit jumps sqrt(2)
> P_b H P_a. Beyond upper bounds, we identify three exact local obstructions
> for the unprocessed physical product. The cubic map M_H produces a nonzero
> n^{-1/2} coefficient; after it vanishes, the quartic product obstruction J_H
> produces a nonzero n^{-1} coefficient; after both vanish, the quintic
> obstruction P_H produces a nonzero n^{-3/2} coefficient. If all three vanish,
> the error is O(n^{-2}). All three coefficient transforms are injective. An
> exact three-record algebraic example has M_H=J_H=0 but P_H nonzero, proving
> that the third branch is attained. The fixed algebra is A intersect
> {H_off}', and the least singular value of the commutator frame C_H defines a
> noncommutative connectivity gap. In the primitive case that gap is the exact
> exponential mixing exponent in diamond norm and is Lipschitz robust under
> Hamiltonian perturbations. Rank-one blocks reduce exactly to twice the
> squared-coupling graph Laplacian. An eight-dimensional rational architecture
> with four qubit blocks is certified irreducible; its gap is the unique root
> in (0.4545,0.4547) of an explicit quartic. Symbolic certificates,
> semidefinite diamond-norm replays, and convergence tests accompany the paper.

## Mathematical scope recorded

For the direct unprocessed CPTP product, v3 proves the exact hierarchy

```text
M_H != 0                         -> Theta(n^(-1/2))
M_H  = 0, J_H != 0              -> Theta(n^(-1))
M_H  = 0, J_H  = 0, P_H != 0   -> Theta(n^(-3/2))
M_H  = 0, J_H  = 0, P_H  = 0   -> O(n^(-2)).
```

The cubic, quartic-product and quintic coefficient transforms are injective.
An exact three-record algebraic architecture attains the quintic branch, so it
is not merely a formal possibility. The paper retains the block-algebra GKLS
limit, fixed-algebra characterization, connectivity gap, perturbative
robustness, rank-one graph boundary and exact rational primitive example.

The manuscript explicitly distinguishes this single-channel physical-product
classification from Möbus's higher-order multi-product formulas using several
sequences and post-processing; the extracted v3 PDF cites Möbus twice.

## Cancelled precursor retained only for audit

The cancelled, non-public v1 artifact had:

- 11 pages and 444,318 bytes;
- PDF SHA-256
  `6F1A48265D87B24561289BADD8DAD1EDE334EB2DE365C7022E36712E8C841625`;
- reproducibility ZIP SHA-256
  `D5B167D3F5477B37DB28256CE628CA47EE0A610C85D3B0BCC86BF26B22877A90`.

These hashes prevent later confusion between local files. They are not a
public v1 record and must not be cited as one.

## Lifecycle

Until a public ai.viXra identifier or moderation result is supplied, v3 remains
**submitted / pending outcome**. This paper does not alter the canonical
Yang–Mills proof-state checkpoint.
