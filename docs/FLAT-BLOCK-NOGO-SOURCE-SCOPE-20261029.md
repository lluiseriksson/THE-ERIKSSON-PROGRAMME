# Flat block no-go: domain, projection and spacing dictionary

Dated reading note, 29 October 2026. This is an analytic scope audit, not a new
Lean theorem, a reproduction verdict, or an extension of the physical hRpoly
frontier. The canonical proof-state contract in `project-state.json` is unchanged.

## Existing result and exact artifacts

The published manuscript *Exact-Kernel Fourier Families Obstruct Every Penalty
Factored Through a Block Map in a Flat Lattice Gauge Form* is already archived as
[ai.viXra 2608.0015v1](https://www.ai.vixra.org/abs/2608.0015) and
[AIRR ARR-2026-7EPM3V3DP796BBRR v1](https://airr.science/papers/ARR-2026-7EPM3V3DP796BBRR/versions/v1/).
Its internal manuscript edition is 1.4; that is distinct from the archive's v1.
It supersedes the proposed scalar-rescaling escape for the **same unrestricted
flat form**. It does not refute gauge-restricted source propagators.

The public PDF SHA-256 is
`48b2b725422263a272d9862621fa723d3d82c9d186dd7151be39c6ff1e3ff2e7`.
The original source anchor `f21539ed0bb880a04078de369bf5cbf063f7b101` covers the
original chain, not the entire later extension. At the inspected branch commit
[`7b25bfb39357406cf61880e3ac0428d7d1ba3449`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/tree/7b25bfb39357406cf61880e3ac0428d7d1ba3449),
`output/pdf/critical_rescaling_fourier_no_go_sources_v1.4.zip` has SHA-256
`ef5501145398b5f672dcdfb66206c1f5f280f2c61b231d2c9ac0e1a4e693f82a`.
The PDF, ZIP and all eleven LF-normalized Lean-body hashes were matched against
the manuscript/manifest in this reading audit. No Lean build was rerun. The
packet's historical Colab execution record remains historical evidence.

The consulted factorized-penalty endpoint is formalized in dimension four.
The manuscript's broader analytic discussion and its higher-frequency min-max
argument must not automatically be described as formalized endpoints.

## Primary-source distinctions

For the same unit-step link values and block geometry, CMP95 (1.11), printed
page 19, normalizes straight line sums by `L^(-(d+1))`; the repository's
`LinearAveraging.linAvg` uses `L^(-d)`. Thus these particular maps differ by
`Q_CMP95 = Q_repo / L`. This is an algebraic comparison before field and spacing
transports, not an identification of every multiscale or covariant source map.

CMP95 (1.18), printed page 20, uses fine spacing `eta = L^(-k)`. Its change of
gauge defines the orthogonal projection `R` onto `Delta ker(Q'_k)` (printed
page 25). The later gauge constraint is `R d* A = 0`, not an axial path constraint
and not a license to replace `R` by the identity.

CMP99 (3.26)-(3.27), printed page 395, uses a background-dependent form with
`D R D*` and a weighted block penalty, then its Dirichlet restriction. A periodic
full-space Hodge operator is not this source operator merely because both have
terms named Laplacian, gauge fixing and Q.

References: T. Balaban, [CMP95, 17-40 (1984)](https://doi.org/10.1007/BF01215753),
and *Propagators for Lattice Gauge Theories in a Background Field*, CMP99,
389-434 (1985), primary archive identifier `1103942769`. The source metadata is
indexed in [the source catalog](source-db/catalogs/spine-backlog.json).

## A one-step axial representative and its projection cost

The following calculation is on a periodic **unit-step** lattice. It is a paper
calculation, not a newly compiled declaration. Set `V = (L N')^d`, `L >= 2`, and
let `phi(r)` be the unit-norm, zero-mean two-coordinate Fourier profile of period
L from the published manuscript. Choose distinct directions i,j, with i traversed
before j in the selected ordered axial paths, and put `u = phi(0)`.
The published field has only `A_i(x) = phi(x_j mod L)` nonzero.

Write `r_i = x_i mod L`, `psi(x) = r_i u`, and `B = A - grad psi`. Then only
component i is nonzero, with

```
B_i(x) = phi(x_j mod L) + g(r_i),
g(r)   = -u       for 0 <= r < L-1,
g(L-1) = (L-1)u.
```

Every within-block axial path sees phase zero during its i segment and never
crosses that block's terminal i edge. Its B integral vanishes. Also both `sum g`
and `sum phi` vanish, so the straight-line block map kills B. Exact periodic
gradients preserve curl. Direct finite sums give

```
||B||^2       = V L,
||curl B||^2  = V lambda_L,
||div B||^2   = 2 V L,
lambda_L      = 4 sin^2(pi/L).
```

The cross term in the norm vanishes by the zero mean of phi. The divergence
count includes L=2: its two edges both have squared jump four. Thus the full
unit-step Hodge Rayleigh quotient on B is `2 + lambda_L/L`; it is not small.

This conclusion also survives the **one-step source projection R**. The scalar
block average of psi is the same constant `(L-1)u/2` on every block. Subtracting
that constant gives `psi_0` in `ker Q'`, without changing its gradient or Laplacian.
Since `div A=0`, `div B` is, up to the sign convention, `Delta psi_0`. The defining
property of R gives `R div B = div B`. In particular this axial representative
fails the later projected-divergence-zero constraint; switching gauges requires
more than renaming the domain. This calculation does not establish an
all-depth, nonabelian or Dirichlet dictionary.

## Why the original Fourier witness is not a source-spacing contradiction

For a lattice of spacing eta, a forward derivative is eta^-1 times the unit-step
difference. The eta^d measure factor occurs in both norms and cancels in a
Rayleigh quotient. For the **original** transverse field, the derivative part
therefore has quotient `eta^-2 lambda_L`. In the one-step comparison eta=1/L,

```
16 <= L^2 * 4 sin^2(pi/L) <= 4 pi^2   (L >= 2).
```

The bounds follow from `2x/pi <= sin x <= x` for `0 <= x <= pi/2`.
The vanishing unit-step witness quotient becomes a positive order-one quantity
at that physical spacing. Its block term is still zero and its divergence is
still zero. This removes this particular purported contradiction; it does not
prove coercivity on all fields or identify the full CMP99 operator.

Any transfer must state separately the block size, RG depth, spacing, field
rescaling, scalar product, gauge projector and boundary conditions. In particular,
letting the no-go's block side grow at unit spacing is not automatically the
source's fixed-block-size, increasing-depth statement.

## What remains open

A source-to-Lean transport for the actual background operator and its uniform
bounds remains open. No Gaussian estimate, Wilson Hessian identification, hRpoly
producer, transfer-matrix spectral gap or continuum construction is supplied here.
The calculations above are suitable as scope checks for that transport, not as
another standalone paper duplicating the existing obstruction family.
