# AREA-LAW VOLUME-UNIFORM PLAN (post-campaign refinement 2)

**Date:** 2026-06-12.  **Status:** design.  Upgrades the COMPLETE
finite-volume area laws (`docs/AREA-LAW-PLAN.md` linearized,
`docs/AREA-LAW-EXACT-PLAN.md` exact-activity) to a constant
independent of the lattice volume `#P`.

## 1. The honest statement of the gap

Both completed laws bound the UNNORMALIZED integral
`‖∫ tr(W_C)·∏_p(activity_p)‖` with a constant `2^{#P}` (crude subset
count) or `2^{#P}·e^{2δN_c·#P}` (exp-series tail).  The physical
object is the NORMALIZED Gibbs expectation `⟨tr W_C⟩_β = numerator/Z`,
and the physical claim is `‖⟨tr W_C⟩‖ ≤ C₀·r^{Area(C)}` with
`C₀ = C₀(N_c, d)` only.  The volume factor must cancel against `Z` —
this is the connected-support (polymer-ratio) resummation, and it is
genuinely campaign-scale.

## 2. Why the repo is unusually well positioned

The ENTIRE pipeline below is banked from the B2/B4 IR-clustering
campaign and the KP layer:

* polymer representation of `Z` and of deformed numerators
  (`L1_GibbsMeasure/PolymerRepresentation.lean`, `WeightedGas.lean`,
  `PolymerFactorization.lean`, Step-2 `Z = Ξ` reconstruction);
* Mayer–Ursell inversion `Ξ = exp(clusterSum)` (`KP/MayerInversion`);
* volume-uniform KP convergence with PINNED clusters
  (`KP/PinnedCluster`, `PinnedWalk`, `PinnedBound`, `SharpKP`,
  `ClusterTail`) — this is exactly the engine that made
  `truncated_correlation_bound` (B4) volume-uniform;
* the N-ality join + per-term dichotomy (`ClayCore/WilsonLoopMonomial`):
  every expansion term whose plaquette support cannot span `C`
  vanishes EXACTLY — this is what converts cluster-size decay into
  AREA decay.

What B4 did for the two-plaquette correlator (observable pinned at
`{p, q}`, clusters connecting them, KP tail in the distance), this
campaign does for the Wilson loop (observable pinned at `supp ∂C`,
clusters spanning the loop, KP tail at size `≥ Area`).

## 3. Brick ladder

| Brick | Content | Status |
|---|---|---|
| V0 | **Loop-tagged expansion of the numerator.** In the linearized class: `∫ tr(W_C)·∏(1+f_p) = ∑_{S ⊆ P} ∫ tr(W_C)·∏_{p∈S} f_p` (banked `integral_mul_prod_one_add`), regrouped by the connected components of `S ∪ supp(C)`: components DISJOINT from the loop's support factor out of the integral (β=0 product factorization over disjoint edge sets — banked `EdgeFactorization` patterns). | open |
| V1 | **Ratio cancellation.** Numerator `= (∑_{S₀ pinned to C} w_C(S₀)) · Z_{P∖nbhd}`-type factorization, and `Z_{P'} / Z_P` controlled by the KP cluster expansion (banked `Ξ = exp(clusterSum)` + volume-monotone cluster bounds).  Output: `⟨tr W_C⟩ = ∑_{S₀ pinned} w_C(S₀) · (Z-ratio)`, `|Z-ratio| ≤ e^{c·|∂-region|}` with `c` volume-independent. | open |
| V2 | **The pinned area tail.** Surviving pinned terms with `|S₀| < Area(C)` are ZERO (the join, banked).  Terms with `|S₀| = k ≥ Area` are bounded by `N_c^{k+1}·δ^k` and counted by the PINNED connected-subset entropy (banked `ConnectedEntropy` + `PinnedBound`): `#{connected S₀ ∋ loop, |S₀| = k} ≤ |C|·ν^k` (lattice coordination `ν = ν(d)`).  Tail: `∑_{k ≥ Area} |C|·(ν·N_c·δ)^k ≤ |C|·(ν·N_c·δ)^{Area}/(1−ν·N_c·δ)` for `δ` in the explicit window. | open |
| V3 | **Assembly:** `area_law_volume_uniform` — `‖⟨tr W_C⟩_β‖ ≤ C₀(N_c, d)·|C|·r^{Area(C)}`, `r = ν·N_c·δ < 1`, all constants volume-free. | open |
| V4 | *(stretch)* The exact-activity version via the E4b dichotomy in place of the linear join. | open |

## 4. Honest difficulties (named, not hidden)

* **D1 — the loop is not a polymer.**  `tr(W_C)` couples ALL edges of
  `C` simultaneously; the component regrouping in V0 must treat
  `supp(C)` as a single pinned vertex.  The B4 analogue treated TWO
  pinned plaquettes; the loop needs the general pinned-set version of
  `PinnedCluster`.  Mechanical but large.
* **D2 — connectivity vs the join.**  The join kills `|S| < Area`
  REGARDLESS of connectivity; but after ratio cancellation the
  surviving sum runs over CONNECTED-to-C supports only.  The kill
  applies verbatim (a subset of the killed terms) — no new
  mathematics, but the bookkeeping of "connected component touching
  supp(C)" needs a clean Finset-graph formulation (banked
  `ClusterGeometry`).
* **D3 — the Z-ratio.**  `Z` restricted to the complement is not
  literally a factor of `Z`; the standard fix is the cluster-expansion
  log-ratio bound.  The repo's `Ξ = exp(clusterSum)` + `KPBound` give
  exactly this, but wiring it to the gauge-marginal `Z` (not the
  abstract gas) is V1's real content.

## 5. Estimated effort

V0: 2–3 sessions (component regrouping over the gauge integral).
V1: 2–4 sessions (the campaign's center of mass — D3).
V2: 1–2 sessions (entropy + tail, heavily banked).
V3: 1 session.  Total 6–10 sessions — comparable to B4.

## 6. What this does not promise

Volume-uniform AREA decay of the lattice Wilson loop at strong
coupling, M3-side (Osterwalder–Seiler regime).  No continuum, no OS
reconstruction, no statement at weak coupling (the physical
confinement regime for d=4 SU(3) continuum — open).  Distance to
Clay: ~0% (<0.1%), unchanged.
