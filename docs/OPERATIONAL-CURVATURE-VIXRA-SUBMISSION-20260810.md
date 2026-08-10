# Operational curvature paper — ai.viXra submission record

Date recorded: **2026-08-10**

Owner-reported operation: **new ai.viXra submission**

Moderation/publication outcome and public identifier: **not recorded here**

## Paper identity

Full title:

*Operational Curvature of the Heisenberg Cut: Exact Diamond Readout, a
Discrete Stokes Law, and Sharp Action Bounds for Dissipative Zeno Holonomy*

- Author displayed on the first page: **Lluis Eriksson**
- Primary category: **Quantum Physics**
- Suggested secondary category: **Mathematical Physics**
- Language: **English**
- Submission date: **10 August 2026**
- Operation: **new submission**

The PDF metadata has no `/Title` value and its `/Author` value is empty, even
though the rendered first page visibly gives the full title and author. This
discrepancy is recorded rather than silently normalized.

## Exact submitted artifact

- Filename: `Operational_Curvature_of_the_Heisenberg_Cut.pdf`
- Pages: **10**
- Figures: **1**
- Bytes: **413,414**
- SHA-256: `16C1224FD17383F9F191FA69622961863C3925076F9A1669024D9335DC3C38B4`

All ten pages were rendered and inspected. No clipping, overlap, broken glyph,
unreadable formula, table failure or figure-composition defect was observed.

Reproducibility package:

- Filename: `Operational_Curvature_Reproducibility.zip`
- Bytes: **403,758**
- SHA-256: `92C91CBAF1F16D76C520ED054256040515647F2ECB2DD7F5F50A4133A5D0BE69`
- ZIP entries: **15**
- Manifest checks: **14/14 PASS**
- Embedded `paper/operational_cut_curvature.pdf`: **byte-identical** to the
  submitted artifact

No public PDF locator, source repository or Git commit was supplied for this
paper. The dashboard therefore records null source anchors rather than
inventing provenance.

## Exact form metadata

Comments (149 characters):

> 10 pages, 1 figure. Exact diamond curvature, a discrete Stokes law, balanced
> semigroup integration, and a sharp qubit action bound. AI use disclosed.

Keywords:

> quantum Zeno effect; Heisenberg cut; nonselective measurement; diamond norm;
> discrete Stokes law; quantum holonomy; GKLS generator; optimal control;
> matrix algebra

Abstract:

> The order of short operations is normally a microscopic detail. We show that
> a fixed degenerate measurement turns it into an operational curvature with an
> exact macroscopic readout. Let E retain a block matrix algebra, and let two
> words apply the same short Hamiltonian kicks in different orders, with the
> same nonselective pinching after every kick. Their leading difference is
> -i tau^2 ad(F) E, where F is the sum of i[h_j,h_k] over pairwise inversions.
> This gives a discrete non-Abelian Stokes law. Its diamond-norm coefficient is
> exactly the largest spectral diameter of a block of F, and therefore fixes
> the leading optimal channel-discrimination advantage. Under first-order
> balance, all permutations have the same dissipator while their geometric
> Hamiltonians differ exactly by F, so local curvature integrates into distinct
> diffusive quantum Markov semigroups. We characterize contextual invisibility,
> the rank-one classical boundary, and inverse-success amplification under
> postselection. Every retained Hamiltonian modulo the block center is
> realizable by a balanced three-kick loop. For a qubit block we prove the sharp
> action law kappa <= S^2/[m tan(pi/m)], attained by regular planar kick
> polygons. An integer-Pauli four-kick architecture saturates the bound and
> supports primitive dissipation. Symbolic, semidefinite, and convergence
> certificates accompany the paper.

## Mathematical scope recorded

For two words containing the same short Hamiltonian kicks in different orders,
with the same nonselective block pinching after every kick, the paper identifies
the leading operational curvature as

```text
W_sigma(tau) - W_pi(tau)
  = -i tau^2 ad(F_sigma,pi) E + O_diamond(tau^3),
```

where `F_sigma,pi` is the sum of `i[h_j,h_k]` over pairwise inversions between
the two orderings. The coefficient in diamond norm is exactly the largest
spectral diameter among the retained blocks of `F_sigma,pi`.

Under first-order balance, the dissipative generator is permutation-independent
while the geometric Hamiltonian changes by exactly this curvature. The paper
also records:

- a discrete non-Abelian Stokes law for kick polygons;
- realization of every retained Hamiltonian modulo the block center by a
  balanced three-kick loop;
- the sharp qubit action inequality
  `kappa <= S^2 / [m tan(pi/m)]`, attained by regular planar polygons;
- an integer-Pauli four-kick saturation architecture compatible with primitive
  dissipation;
- exact symbolic and semidefinite checks over all **24** four-kick
  permutations, including the reported action gap **4**;
- a numerical audit over **1,000** seeded kick polygons.

The bibliography was compared with quasi-Zeno dynamics, open-system Zeno
dynamics and measurement-driven holonomic control. This record preserves that
positioning without converting it into an unverified claim of priority.

## Lifecycle

Until a public ai.viXra identifier or moderation result is supplied, the paper
remains **submitted / pending outcome**. It does not alter the canonical
Yang--Mills proof-state checkpoint.
