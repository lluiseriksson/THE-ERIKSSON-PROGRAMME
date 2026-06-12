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
| V0 | **Loop-tagged expansion of the numerator.** In the linearized class: `∫ tr(W_C)·∏(1+f_p) = ∑_{S ⊆ P} ∫ tr(W_C)·∏_{p∈S} f_p` (banked `integral_mul_prod_one_add`), regrouped by the connected components of `S ∪ supp(C)`: components DISJOINT from the loop's support factor out of the integral.  **V0-1 CLOSED** (`L1_GibbsMeasure/SupportFactorization.lean`, oracle clean): `DependsOnPos` (positive-edge-support dependence, with `mono`/`mul`/`finset_prod` calculus), `edgeSupport`/`plaquettePosSupport`, `dependsOnPos_comp_wilsonLine` (ONE lemma covers traces, linearized AND exponential activities via post-composition `φ : G → ℂ`), `integral_mul_of_disjoint_pos_deps` (two-block independence over `gaugeMeasureFrom`, transported along `gaugeConfigMEquiv`), `integral_mul_prod_of_disjoint_support` (the split headline) and its Wilson instantiation `integral_wilson_obs_mul_prod_split`.  House note: name `plaquettePosSupport` — `plaquetteSupport` is taken by `PolymerExpansion` at the signed-edge level.  REMAINING in V0 — **V0-2, the component regrouping** (designed 2026-06-12): partition each `S ⊆ P` of the powerset expansion as `S = S₀ ⊎ S_far` with `S₀` the union of the `plaqComponents` (banked in `ClusterGeometry.lean`: `plaqComponents_biUnion_eq`, `_support_disjoint`, `_not_touching`, `_isConnectedPolymer`, `_disjoint`) touching the loop's support and `S_far` the rest; then V0-1's `integral_mul_prod_of_disjoint_support` splits `∫ tr(W)·∏_S f = (∫ tr(W)·∏_{S₀} f)·(∫ ∏_{S_far} f)`.  **Named seam:** `ClusterGeometry` connectivity/touching lives at the SIGNED-edge level (`plaquetteSupport : Finset (ConcreteEdge d N)`, `PolymerExpansion`), while V0-1's independence is at the POSITIVE-edge level (`plaquettePosSupport : Finset (PosEdge d N)`); **The feared seam DISSOLVED** (V0-2 opening, CLOSED, oracle clean): `PolymerExpansion.plaquetteSupport` was already at the positive-edge level (`{(p.edges i).pos}`), so the bridge is an outright equality — `plaquettePosSupport_eq : plaquettePosSupport p = plaquetteSupport p` (ext + mem-level simp; house note: simp normalizes a 4-element list-map membership to a 4-way disjunction WITHOUT a trailing `∨ False`, so the rintro pattern is `(rfl \| rfl \| rfl \| rfl)`, not five cases) and `dependsOnPos_plaquette_obs'` states plaquette-observable dependence directly against `plaquetteSupport` — the exact interface `plaqComponents_support_disjoint`/`_not_touching` speak.  **V0-2 CLOSED** (oracle clean): `nearLoop es S` (the biUnion of the `plaqComponents` touching `edgeSupport es`) with `nearLoop_subset`, `mem_plaqComponents_of_mem`, `farLoop_disjoint_edgeSupport`, `near_far_support_disjoint` (different components ⇒ support-disjoint, via `plaqComponents_support_disjoint`), and the headline `integral_wilson_obs_regroup`: `∫ φ(W_C)·∏_{p∈S} f_p = (∫ φ(W_C)·∏_{nearLoop} f_p)·(∫ ∏_{S∖nearLoop} f_p)` for ANY activities with `DependsOnPos (f p) (plaquetteSupport p)`.  **V0 is COMPLETE** — next: V1, the ratio cancellation (sum the far factors back into `Z`-restricted form and control `Z`-ratios by the cluster expansion). | **V0 closed** |
| V1 | **Ratio cancellation.** Numerator `= (∑_{S₀ pinned to C} w_C(S₀)) · Z_{P∖nbhd}`-type factorization, and `Z_{P'} / Z_P` controlled by the KP cluster expansion (banked `Ξ = exp(clusterSum)` + volume-monotone cluster bounds).  Output: `⟨tr W_C⟩ = ∑_{S₀ pinned} w_C(S₀) · (Z-ratio)`, `|Z-ratio| ≤ e^{c·|∂-region|}` with `c` volume-independent.  **V1-a CLOSED** (oracle clean): `prod_one_add_eq_sum_powerset` (ℂ-valued binomial over arbitrary `F`) + `sum_integral_prod_eq_integral_prod_one_add` — the far resummation `∑_{T⊆F} ∫ ∏_T f = ∫ ∏_F (1+f)` (the restricted-`Z` object the ratio divides against).  NEXT (V1-b, the hard brick): the fiber bijection of the powerset sum — `S ↔ (S₀, T)` with `nearLoop es S₀ = S₀` pinned and `T ⊆ farRegion es S₀`.  **Forward half CLOSED** (oracle clean): `farRegion` (the index set of the far subsets) and `sdiff_nearLoop_subset_farRegion : S ∖ nearLoop es S ⊆ farRegion es (nearLoop es S)` — immediate from the V0-2 support lemmas since `plaquetteTouches = ¬Disjoint` of supports.  **Remaining (the genuinely hard half), step (1) CLOSED:** `mem_nearLoop_iff_reachable` — `p ∈ nearLoop es S ↔ ∃ q : ↥S, Reachable (fromRel plaquetteTouches) ⟨p⟩ q ∧ supp q meets the loop` (oracle clean).  House notes: the `biUnion id` wrapper leaves `id (B.image val)` in membership hypotheses — `simp only [id_eq]` before `rw [Finset.mem_image]`; and `Finpartition.mem_part_ofSetoid_iff_rel.mpr` cannot elaborate argument-first (its implicits stay metas) — ALWAYS ascribe the resulting membership in a `have` with the full `(Finpartition.ofSetoid …).part …` type; `Setoid.refl` needs an INSTANCE, use an ascribed `SimpleGraph.Reachable.refl` instead.  Steps (2) and (3) ALSO CLOSED (oracle clean): `walk_confined` — a `↥(S₀∪T)`-walk from a `T`-vertex stays in `T` under no cross-touching (`induction W with \| @cons u v w h W ih` to name the implicit vertices; `fromRel_adj` + `Disjoint.symm` per step); `reachable_union_of_reachable` — `S₀`-reachability transports along the inclusion hom via `Reachable.map` (house note: extracting `a = b` from an equality of subtype-IMAGES must go through an UNASCRIBED `have h2 := congrArg Subtype.val h` — any expected-type pressure re-routes the implicits to the wrong subtype).  Steps still open (est. 1 session): (4) **walk descent** — a union-walk with endpoints avoiding `T` descends to an `S₀`-walk (converse induction); then (5) `nearLoop es (S₀ ∪ T) = S₀` for `T ⊆ farRegion es S₀` and the `Finset.sum_nbij'` fiber reindexing close V1-b. | V1-a + V1-b(1–3) closed |
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
