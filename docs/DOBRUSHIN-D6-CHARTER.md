# D-6 CHARTER — the spectral endpoint: specRatio away from 1, uniformly in
# the extent, inside the Dobrushin window

Registered before any Lean of the rung.  Lineage: docs/DOBRUSHIN-D3-CHARTER.md
(D-1..D-4 closed), D-5 in flight at 8e302d62f.  Gates: G18-G20 of
scripts/judge_dobrushin_d6.py, committed WITH this charter, run on the Colab
plane before fabrication.

## The target, stated with its quantifiers

For the coupled Z_2 transfer kernel `T_L` (spatial coupling gamma, time
coupling beta) with Perron data `(lam_L, Omega_L)` and the normalised
operator `M_L = T_L / lam_L`:

    THEOREM (target).  If 2 tanh|beta| + 2 tanh|gamma| <= alpha < 1, then
    there exists m > 0 with, for EVERY extent L,
        ‖projectedTransfer M_L Omega_L‖ <= exp(-m).

The window and m are fixed before L.  This is the volume-uniform statement
the paper's frontier names open; in the disordered window it would prove the
uniformity wall is a property of the ordered phase only.

## Why this is now an assembly, not a leap

The consumer `volumeUniform_gap` (TransferGap.lean, elaborated) takes decay
of `connCorr (M_L) (Omega_L) v n` at a COMMON rate r with a prefactor C that
MAY depend on (L, v).  Only the rate must be uniform.  The uniform rate is
exactly what D-5 certifies at the measure level: alpha^d decay for the
rectangle family, constants fixed before the volume.  What remains is the
translation of `connCorr` into rectangle-measure quantities:

* B-1 (STRIP IDENTITY, finite sums, no limits).  For v a slice observable,
  `<v, T_L^n v>` IS the free-boundary strip Gibbs sum over [0,n] x L with
  v-weighted ends; `<Omega, v>` is paper 9's dressed expectation.  All
  finite; the tree already carries the dressing identity (SpatialGibbs) and
  `connCorr_eq` (TransferGap).
* B-2 (PREFACTOR CONTROL, per-extent only).  Normalisations Z_strip/lam^n
  and boundary overlaps converge at FIXED L by the strict Perron gap
  (paper 8); their limits and speeds may depend on L freely, because the
  consumer's C may.  No uniform Perron gap is assumed anywhere — assuming it
  would be assuming the conclusion.
* B-3 (RATE TRANSPORT).  D-5's alpha^{Manhattan} dominates alpha^{time
  separation}; the strip correlators inherit rate alpha with (L, v)-dependent
  prefactor.  Feed volumeUniform_gap; read off m = -log alpha.

Failure remains possible and will be recorded: the risk concentrates in B-3's
bookkeeping between free-boundary strips (what D-5 bounds) and the
v-weighted ends (what B-1 produces).  If the composed prefactor cannot be
shown finite, the rung dies there and the charter says so.

## Gates (scripts/judge_dobrushin_d6.py, this commit)

* G18  STRIP IDENTITY, exactly.  On registered small (L, n) and in-window
  cells: `<v, T^n v>` computed by dense linear algebra equals the
  free-boundary strip Gibbs sum computed by full enumeration, to 1e-10,
  for a registered basis of observables v.
* G19  THE TARGET'S NUMERIC SHADOW.  specRatio(M_L) <= window, for
  L = 2..8, on three in-window cells: the second-eigenvalue ratio of the
  normalised coupled kernel sits UNDER the Dobrushin window (the target
  inequality, measured).  One out-of-window control cell is measured and
  REPORTED without a pass condition, because the theorem says nothing there.
* G20  PREFACTOR CONVERGENCE AT FIXED L.  Z-ratio rho_n = Z_{n+1}/(lam Z_n)
  and end-overlap converge geometrically at rate specRatio(L) at fixed L
  (three L values, one cell): |rho_n - rho_inf| <= K * specRatio^n with K
  fitted at n=1 and verified for n up to 8.

No assert; explicit counters; both interpreter modes; Colab plane.

## Order of work

1. D-5 green and oracled (in flight).  2. G18-G20 pass on the plane.
3. B-1 fabrication (strip identity in Lean).  4. B-2 (per-extent limits).
5. B-3 (assembly into volumeUniform_gap).  6. Paper v6: the theorem, or the
   recorded corpse.  Every step oracled before the next begins.

ROLES: this desk fabricates; it does not audit itself; no score anywhere.
