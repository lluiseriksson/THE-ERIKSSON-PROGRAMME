# Dobrushin matrix paper — v8.1 viXra v2 replacement record

Date recorded: **2026-08-04**

Operation: **v2 replacement submitted over the live v1**

viXra state: **pending administrator; do not resubmit**

Public article identifier: **not yet recorded**

The live predecessor is the v7.1 manuscript submitted as `[v1]` on
**2026-08-03 20:07:25**. This replacement rewrites the complete viXra record;
the four metadata fields below are therefore recorded in full rather than as a
delta.

## Article title

*The Row Sums Were the Method, Not the Theorem: a Machine-Checked Chain from
a Positive Weight to Exponential Decay of Correlations, and a Misattributed
Uniformity Wall*

## Authors and category

- Authors: Lluis Eriksson
- Category: Mathematical Physics

## Abstract submitted with v2

> A formal Lean 4 development revisits a two-dimensional spatial transfer kernel whose earlier uniform spectral argument relied on constant row sums. We show that the loss of row-sum constancy obstructs that method, not the conclusion. With no sorry and no project axiom, we prove twelve machine-checked theorems.
>
> The chain establishes the sharp field-uniform one-bond influence envelope tanh J; assembles these bounds into a finite-volume Dobrushin matrix; proves a volume-independent resolvent estimate under row-sum bounds alpha < 1 without assuming constant rows; mechanises Dobrushin's comparison inequality with the attained 1/4 covariance constant; constructs Gibbs measures, heat-bath kernels and intrinsic influence matrices from arbitrary strictly positive finite weights; and specialises to anisotropic Ising interactions. For L x T rectangles with free boundary, the condition 2 tanh|beta| + 2 tanh|gamma| <= alpha < 1 yields exponential decay of correlations with beta, gamma, alpha and the prefactor fixed before the volume quantifiers.
>
> The transport into the operator formulation is closed: an exact finite band identity relating endpoint covariances to matrix elements; an abstract theorem showing that a common exponential decay rate for band covariances - a hypothesis on finite path measures, carrying no operator, norm or spectrum - implies a uniform positive gap for a family of projected transfer operators; a Perron-boundary tilt identity that preserves the decay rate while absorbing boundary costs into extent-dependent constants; an exact currying identification of the free strip measure with the rectangle Ising measure; and the resulting corollary: inside the window there is one m > 0 bounding the projected transfer operator of the coupled kernel's normalised Perron data by exp(-m) at every extent, with m = -log alpha.
>
> Numerical measurements at L <= 12 provide counterevidence to attributing spectral degeneracy solely to nonzero spatial coupling. No infinite-volume state, thermodynamic limit or boundary-condition independence is constructed; the window is sufficient, not sharp. The underlying Dobrushin mathematics is classical; the contribution is a non-vacuous, reproducible mechanisation and composition of the full chain, ending at a volume-uniform operator gap. No consequence for Yang-Mills theory is claimed.

## Comments submitted with v2

Exactly 192 characters:

> 25 pages. Lean 4, no sorry, no project axiom. Twelve machine-checked theorems: positive weight to exponential decay, and through an abstract transport theorem to a volume-uniform operator gap.

## Exact PDF submitted

- Edition: v8.1
- Length: 25 pages
- Paper commit: [`1b8f7012ccc7b92d08129a6385a86d97fdfdf623`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/1b8f7012ccc7b92d08129a6385a86d97fdfdf623)
- [Exact PDF at the paper commit](https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/1b8f7012ccc7b92d08129a6385a86d97fdfdf623/papers/dobrushin-matrix/dobrushin_matrix.pdf)
- PDF SHA-256: `18A02AC2D5AECC1090396E0EFF6BA6207E66A4D10AD501E6F918E44F28F9CC92`
- PDF size: 501,466 bytes
- PDF Git blob OID: `fee63a8b564a9bb924fd9df3f7727d8c11c35345`
- [Repository ZIP at the paper commit](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/archive/1b8f7012ccc7b92d08129a6385a86d97fdfdf623.zip)

The PDF was downloaded from the raw commit URL and its digest and byte count
were recomputed. An independent PDF parser counted 25 pages.

## Version boundary and remaining work

The v1/v7.1 record counted eleven theorems and left one concrete transport
discharge open. The v2/v8.1 record counts twelve theorems and states the
currying/feed composition and resulting volume-uniform projected-operator gap
as closed within the printed finite-volume window.

This does not construct an infinite-volume state, a thermodynamic limit, or
boundary-condition independence. D-7, the infinite-volume step, remains the
next substantive mathematical layer. No consequence for Yang--Mills theory
is claimed.

At the time of recording, the paper commit is reachable from remote branch
`d3-closure` and is not an ancestor of `main`. This submission record does not
replace the canonical `main` build checkpoint or assert integration.
