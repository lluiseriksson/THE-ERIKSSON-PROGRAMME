# D-6 / B-2+B-3 DESIGN NOTE — the transport route, registered before any
# Lean of B-2

Lineage: docs/DOBRUSHIN-D6-CHARTER.md and its Amendments 1-2 (binding).
Status at registration: B-1 (`YangMills/OS/DobrushinBridge.lean`) fabricated,
pass 2 in verification on the plane; gates G18-G20 passed 60/60 both modes
(ledger Addendum 594).  The gates of THIS note are G21-G23 of
`scripts/judge_dobrushin_d6b.py`, committed WITH it; they run on the Colab
plane and must pass BEFORE any Lean of B-2 is written.  Nothing below is a
theorem until it is.

## What B-1 turned out to buy, and the consequence for the module split

`band_covariance_eq` (B-1) makes the band covariance of `f, g` at time
separation `n` EQUAL to the matrix element of `M^n` at the centred dressed
observables, over `∑ Ω²`.  Meanwhile the consumer `volumeUniform_gap`
(TransferGap.lean) wants, per index `i` and EVERY Hilbert vector `v`, a bound
`|connCorr (T_i) (Ω̂_i) v n| ≤ C · r^n` with only `r` uniform.  The distance
between the two is ONE exact identity plus packaging, so B-2 and B-3
of the charter land as TWO modules:

* `DobrushinTransport.lean` — the ABSTRACT side (Amendment 2 theorem (i)).
* `DobrushinCorollary.lean` — the Dobrushin-Ising witness (theorem (ii)).

## Module 1: DobrushinTransport.lean (abstract; no Ising, no Dobrushin)

1. PACKAGING.  For finite `X`, the matrix `M` acts on `EuclideanSpace ℝ X`;
   the continuous linear map is built from `Matrix.mulVec` and finite
   dimensionality, with the power-compatibility lemma
   `(T_op)^n v = (M^n).mulVec v` proved by elementary induction (house
   style; no C*-API).  Named pin risk: the `Matrix.toEuclideanCLM` /
   `WithLp.toLp` apply-lemma names; fallback is the fully hand-rolled CLM,
   which loses nothing because every proof below is entrywise anyway.
   Vacuum: `Ω̂ = (∑ Ω²)^{-1/2} • Ω`; `VacuumTransfer T_op Ω̂` from symmetry,
   `M Ω = Ω`, and `∑ Ω² > 0`.

2. THE B-2 IDENTITY (the whole content of "prefactor control").  For every
   `v : X → ℝ`, with `f_v = v / Ω` (defined by Perron positivity):

       connCorr T_op Ω̂ v n  =  (∑ Ω²) · bandCov M Ω n f_v f_v

   where `bandCov M Ω n f g := (∑_paths f(x0) g(xn) bandW) / (∑ Ω²)
   − bandE f · bandE g` is the MEASURE-level band covariance of B-1.
   Exact, every `n` (including `n = 0`); proof = `band_covariance_eq`
   plus `(f_v · Ω) = v` pointwise.  The prefactor `∑ Ω²` and any constant
   the decay hypothesis supplies for `f_v` are absorbed into `C_{i,v}` —
   the consumer permits it (∃C after ∀v).  Binding non-goals restated
   from Amendment 2: no bound on `min Ω`, on `‖f_v‖∞`, no constant common
   to indices, no uniform Perron vector, no optimal prefactor.

3. THE ABSTRACT TRANSPORT THEOREM (public theorem (i)).  Data: an index
   family `i : ι` of finite slice types `X i`, symmetric kernels with
   strictly positive entries, Perron data `(λ_i, Ω_i)` normalised to
   `M_i Ω_i = Ω_i`, `Ω_i > 0`.  Hypothesis (THE BAND-COMPATIBILITY /
   ANTI-CIRCULARITY CLAUSE, Amendment 2(i)): there is `r`, `0 < r < 1`,
   with, for every `i` and every slice observable `f : X i → ℝ`, some
   `C ≥ 0` such that `|bandCov M_i Ω_i n f f| ≤ C · r^n` for all `n`.
   Conclusion: `∃ m > 0, ∀ i, ‖projectedTransfer T_i Ω̂_i‖ ≤ exp (−m)`.
   Proof: identity 2 feeds `volumeUniform_gap` with `C' = (∑ Ω²) · C`.
   The hypothesis is stated on PATH SUMS of the band weight — no operator,
   no norm, no spectrum occurs in it; the identification measure↔operator
   is B-1's THEOREM, not an assumption.  `r` is common; everything else is
   per-`(i, v)`.  B-3's "rate flexibility" is not needed here: the rate
   transports unchanged.

## Module 2: DobrushinCorollary.lean (the witness; where the boundary cost
## actually lives)

The hypothesis of module 1 must be DISCHARGED for the coupled Z₂ kernel
`T_L = diag(√w_γ) K_β diag(√w_γ)` in the Dobrushin window.  The route,
with the two dressings kept explicitly apart (Amendment 2's second named
failure mode):

4. THE TILT IDENTITY.  The band measure (Ω-boundary, B-1's object) is the
   free-boundary strip Gibbs measure (paper 9's `gibbsWeight`, = the D-5
   rectangle measure) TILTED at the two end slices by

       ψ = Ω / √w        (NOT Ω · √w — getting this factor wrong is
                          exactly the conflation the charter names; gate
                          G22 measures the identity with ψ = Ω/√w)

   via `E_band[F] = E_free[F ψ₀ ψ_n] / E_free[ψ₀ ψ_n]`, because
   `bandW = ψ(x₀) · gibbsWeight · ψ(x_n) / λ^n` and both `λ^n` and the
   free partition function cancel in the ratio.

5. THE FIVE-TERM FORMULA.  With `a = f·ψ` at slice 0, `b = g·ψ` at slice
   `n`, `p = ψ₀`, `q = ψ_n`, and all covariances/expectations in the FREE
   measure:

       bandCov(f,g,n) · E[pq]²
         = C(a,b)·C(p,q) + C(a,b)·E[p]E[q] + E[a]E[b]·C(p,q)
         − C(a,q)·C(p,b) − C(a,q)·E[p]E[b] − E[a]E[q]·C(p,b)

   (the `E[a]E[b]E[p]E[q]` terms cancel).  Every surviving term carries at
   least one slice-0-vs-slice-n free covariance.  The band marginals are
   n-independent (`bandE`, proved in B-1), so the LHS is the bandCov of
   the abstract hypothesis, not merely a tilted covariance.

6. THE DENOMINATOR FLOOR.  `E_free[ψ₀ψ_n] ≥ (min ψ)² > 0`, uniformly in
   `n` at fixed `L`, by pointwise positivity of ψ on the FINITE slice
   space — no decay input, no limit.  The floor may depend on `L` freely
   (`C_{L,v}` absorbs it; Amendment 2 permits dependence on `min Ω`).

7. THE D-5 FEED.  Each free covariance in 5 is `covar (gibbsMu
   (isingWeight (rectJ β γ)))` of observables supported on the two end
   slices, through the currying bijection between paper 9's path space
   `Fin (n+1) → (Fin L → Fin 2)` and D-5's rectangle `(Fin L × Fin T) →
   Fin 2` (THE GEOMETRY BRIDGE — the piece of this module with real
   fabrication risk; `SpatialReconstruction`'s two-geometry work is prior
   art in the tree).  Every site pair (end slice 0, end slice n) has
   `rectDist ≥ n`, so `ising_covar_exp_decay` (D-4b general form) gives
   `|C(·,·)| ≤ (∑ osc)·(∑ osc)·α^n / (4(1−α))` — the double oscillation
   sum may grow with `L`, which is the growth Amendment 2's B-3 spec
   permits.

8. ASSEMBLY (the "composed prefactor finite" claim).  6-term bound, each
   term ≤ (explicit product of oscillation sums, sup norms, and the
   floor)·α^n, using `α^{2n} ≤ α^n`; total `C_{L,f} · α^n`.  Gate G23
   measures the ASSEMBLED bound against the measured band covariance —
   the corpse-detector for this module: if the assembly is wrong, it dies
   at the gate, before any Lean.

9. THE COROLLARY (public theorem (ii)).  Window `2tanh|β| + 2tanh|γ| ≤ α
   < 1` ⟹ the band-decay hypothesis of module 1 for the coupled-kernel
   family over extents `L` ⟹ `∃ m > 0, ∀ L, ‖projectedTransfer‖ ≤
   exp(−m)`.  Ising certifies the bridge is inhabited; the theorem
   survives Onsager-Kaufman.

## Order of work and failure recording

G21-G23 pass on the plane → module 1 fabricated and oracled → module 2
fabricated and oracled → paper v7 (theorem or recorded corpse).  If the
geometry bridge (7) or the assembly (8) dies in Lean, module 1 STANDS as
the public abstract theorem and the corpse is recorded at the point of
death; the Ising-only fallback of Amendment 1 is explicitly not taken —
the abstract theorem is first, per the finish line: "prove the abstract
bridge and use Ising to show it lives."

ROLES: this desk fabricates; it does not audit itself; no score anywhere.
