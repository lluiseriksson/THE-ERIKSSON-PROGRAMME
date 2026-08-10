# Block-record Zeno diffusion paper — ai.viXra submission record

Date recorded: **2026-08-10**

Latest owner-reported operation: **new paper sent to ai.viXra**

Moderation/publication outcome and public identifier: **not recorded here**

## Provenance note

The preparation handoff bundled with the artifact says that no external upload
was performed at that stage. The owner's later message explicitly reports that
the paper was sent; this later statement is the lifecycle fact recorded here.
No public ai.viXra identifier, public PDF URL, source repository or Git commit
was supplied. Accordingly, the submission status is owner-attested while the
local artifact identity below was independently recomputed.

## Paper identity

Full submission title:

*Noncommuting Block Measurements Generate Quantum Diffusion: A Sharp
Diamond-Norm Zeno Limit, a Noncommutative Connectivity Gap, and an Exact
Irreducible Architecture*

- Author displayed on the first page: **Lluis Eriksson**
- Primary category: **Quantum Physics**
- Suggested secondary category: **Mathematical Physics**
- Language: **English**
- Version date: **10 August 2026**

The embedded PDF title is the shorter *Noncommuting Block Measurements
Generate Quantum Diffusion*. Its embedded `/Author` field is empty even though
the first page visibly names `Lluis Eriksson`. This metadata discrepancy is
recorded rather than silently normalized.

## Exact submitted artifact

- Filename: `Block_Record_Projections_Generate_Quantum_Diffusion_Definitive.pdf`
- Pages: **11**
- Figures: **2**
- Bytes: **444,318**
- SHA-256: `6F1A48265D87B24561289BADD8DAD1EDE334EB2DE365C7022E36712E8C841625`

The PDF was rendered page by page. No clipping, overlap, broken glyphs or
composition failure was observed in the 11-page object.

Reproducibility package:

- Filename: `Block_Record_Projections_Definitive_Reproducibility.zip`
- Bytes: **446,484**
- SHA-256: `D5B167D3F5477B37DB28256CE628CA47EE0A610C85D3B0BCC86BF26B22877A90`
- ZIP entries: **17**
- Manifest checks: **16/16 PASS**
- Embedded paper PDF: **byte-identical** to the submitted artifact

The package contains the LaTeX source, exact and numerical certificates,
verification programs, two vector figures, pinned dependencies, claim ledger,
research memo, submission sheet and SHA-256 manifest. Neither the PDF nor the
ZIP is asserted to be publicly downloadable from this repository.

## Exact form metadata

Comments:

> 11 pages, 2 figures. The supplement contains deterministic symbolic and
> numerical certificates, exact rational irreducibility data, diamond-norm SDP
> replays, pinned dependencies, and SHA-256 hashes. The manuscript discloses
> AI assistance. The sharp rate theorem concerns the unprocessed iterate of
> one CPTP block-measurement cycle; it is distinct from higher-order
> multi-product Zeno extrapolation using several sequences and post-processing.

Keywords:

> quantum Zeno effect; nonselective measurement; quantum Markov semigroup;
> diamond norm; conditional expectation; irreducibility; spectral gap; GKLS
> generator; noncommuting projections

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
> P_b H P_a. Beyond an upper bound, we identify the exact cubic obstruction
> M_H=(i/2)[E ad_H E,E ad_H^2 E] and prove a sharp dichotomy for the direct
> physical product: M_H nonzero gives a nonzero n^{-1/2} asymptotic coefficient,
> whereas M_H=0 gives O(n^{-1}); central retained block Hamiltonians form a
> transparent sufficient class. The fixed algebra is A intersect {H_off}', and
> the least singular value of the commutator frame C_H defines a
> noncommutative connectivity gap. In the primitive case that gap is the exact
> exponential mixing exponent in diamond norm and is Lipschitz robust under
> Hamiltonian perturbations. Rank-one blocks reduce exactly to twice the
> squared-coupling graph Laplacian. An eight-dimensional rational architecture
> with four qubit blocks is certified irreducible; its gap is the unique root in
> (0.4545,0.4547) of an explicit quartic. Symbolic certificates, semidefinite
> diamond-norm replays, and convergence tests accompany the paper.

## Mathematical scope recorded

The definitive version identifies the exact cubic obstruction

```text
M_H = (i/2) [E ad_H E, E ad_H^2 E]
```

and proves the direct-product dichotomy: a nonzero obstruction produces a
nonzero `n^(-1/2)` asymptotic coefficient, while `M_H = 0` gives `O(n^(-1))`.
The statement concerns one unprocessed CPTP block-measurement cycle. The paper
explicitly distinguishes it from Möbus's higher-order multi-product Zeno
formulas using several sequences and post-processing; the extracted PDF cites
Möbus twice.

The reported `6.01/10` evaluation is retained as a **technical internal note**,
not as external peer review. The package records the conjunction of exact
local expansion, diamond-norm diffusive limit, GKLS form, fixed algebra,
connectivity gap, perturbative robustness, rank-one boundary and an exact
rational primitive example. It does not claim that the general Zeno,
Chernoff-product, GKLS or quantum-Markov tools are individually new.

## Lifecycle

Until a public ai.viXra identifier or moderation result is supplied, this
submission remains **submitted / pending outcome**. Because no public locator
or Git commit was supplied, the dashboard records null source anchors instead
of inventing provenance. This paper does not alter the canonical Yang–Mills
proof-state checkpoint.
