# `hRpoly` CAMPAIGN — the cluster-expansion-with-holes activity bound

**Live status (2026-06-20).** Core green at **8290 jobs**.  The campaign has
already closed substantial substrate: animal counting, cube summability,
marginal-coupling summability, exponential-decay kernel calculus, Schur/PSD
kernel bounds, Gaussian MGF bounds, concrete finite-dimensional Gaussian
construction, finite-range/resolvent decay, explicit shell-growth summability,
the source-faithful Appendix-F target-family compiler, and the first finite
quantitative connected-activity majorant.  The remaining genuinely analytic
target is still `hRpoly`: the concrete Yang-Mills activity-decay estimate for
the actual gauge RG operator, plus the Appendix-F connected-cover entropy and
activity estimates that convert the finite connected-cover sum into Dimock's
exponential bound.  The source-faithful finite modified-metric stitching
`d_M(Y)+1 ≤ Σ_X(d_M(X)+1)` is now theorem-fed; the analytic bound on the
resulting cover sum is still open.

**Original date:** 2026-06-12.  This is the source-grounded campaign document
for discharging `hRpoly`, the **sole remaining genuinely-analytic carried
input** of the end-to-end UV conditional.

## 0. The target

The end-to-end conditional carries
`hRpoly : ∀ t k, |R_{t,k}| ≤ A·e^{−c₀t}·g_k^{κ₀}` — the bound on the
renormalization-group remainder of the two-point function at distance `t`
and scale `k`.  In Bałaban/Dimock this is the OUTPUT of the per-scale RG
step, whose `R_k` is a sum of **renormalized polymer activities** `H^#(Y)`
over boundary-touching polymers `Y`.  Discharging `hRpoly` means proving
that bound from the construction, not assuming it.

## 1. The two genuinely-hard analytic theorems

`hRpoly` decomposes into TWO hard pieces (and one combinatorial input,
largely reduced):

**(A) The fluctuation integral → raw activity bound (Dimock §3.8).**
The Gaussian integration over the fluctuation field `W_k` (covariance
`C_{k,Ω}`, the renormalized propagator) produces local polymer activities
`H_k(X, φ)` with the *raw* exponential bound
`|H_k(X)| ≤ H₀·e^{−κ·d_M(X, mod Ω^c)}`, `H₀` tied to the running coupling
`g_k^{κ₀}` and the field size.  **Needs:** the renormalized Gaussian
measure + its covariance bounds (CMP 95–96; `docs/UV-S2-GAUSSIAN-PLAN.md`
G5).  Mathlib has the `IsGaussian` framework (G1–G4 built) but not the
lattice covariance operator with the Combes–Thomas decay.

**(B) The cluster expansion with holes (Dimock II Appendix F / III).**
Propagates the raw bound (A) to the renormalized activities `H^#(Y)`:
given `|H(X)| ≤ H₀·e^{−κ d_M(X, mod Ω^c)}`, `H₀ ≤ c₀`, `κ ≥ 3κ₀+3`, and
the geometric summability `∑_{X⊇□} e^{−κ₀ d_M(X, mod Ω^c)} ≤ K₀`, then
`Ξ = exp(∑_Y H^#(Y))` with
`|H^#(Y)| ≤ O(1)·H₀·e^{−(κ−3κ₀−3) d_M(Y, mod Ω^c)}`
(`docs/BALABAN-SOURCE-BOUNDS.md` §5).  **Constants flagged for
verification** (see §4).

**(C) The geometric summability** `∑_{X⊇□} e^{−κ₀ d_M} ≤ K₀` is **CLOSED as
graph combinatorics** (ledger Add. 57–60): the animal count `c_n ≤ (Δ²)ⁿ`
(`rooted_connected_card_le_pow`) composed with `polymer_weight_summability`
gives `rooted_connected_weight_summable` (`RG/AnimalTour.lean`):
`∑_Y q^{#Y} ≤ (1−Δ²q)⁻¹` for `Δ²q < 1`.  **Closed: the discrete modified-metric summability**
(identifies Dimock `M`-cube polymers with rooted connected sets, `q = e^{−κ₀}`).

## 2. What is reusable (do NOT rebuild)

* **The abstract Mayer/Kotecký–Preiss cluster expansion** is BUILT:
  `KP.PolymerSystem`, `KP.IsCluster`, `KP.ursell`/`ursellComplete`,
  `KP.clusterSum`, `KP.partition_eq_exp_clusterSum` (+ `_of_kp`,
  `_restrict`, `_singlePolymer`), `KP.cluster_series_summable`,
  `KP.cluster_sum_le`, `KP.kp_per_size_bound` (the per-size/animal-weighted
  geometric bound).  This is the hole-FREE `Ξ = exp(∑ clusters)` + KP
  convergence.
* **The gauge-RG summation/reduction layer** is BUILT:
  `RG.polymer_remainder_bound` (`|∑ H(Y)| ≤ amp·K₀`),
  `RG.geometric_size_summability` (the geometric convergence core),
  `RG.polymer_weight_summability` (`hwK` ⟸ animal-count `c_n ≤ Cⁿ`).
* **The free RG step** (G1–G4): `RG.linAvgCLM`,
  `RG.covarianceBilinDual_map_clm`/`_le` (covariance `↦ Q C Qᵀ`,
  contracts by `‖Q‖²`); `RG.linAvg_l2_contraction` (`L^{2−d}`).
* **The coupling-flow side** is fully discharged:
  `RG.coupling_flow_bridge`, `RG.logistic_geometric_decay`,
  `RG.inv_coupling_linear_growth` (asymptotic freedom).

## 3. New content — the brick ladder

| Brick | Content | Kind | Status |
|---|---|---|---|
| **P0** | this spec | design | done |
| **P1a** | **Bounded-degree walk-count engine** `card_walks_length_le_degree_pow`: for any `SimpleGraph` of max degree `≤ Δ`, the number of length-`n` walks from a fixed vertex is `≤ Δⁿ`.  The combinatorial engine behind the animal count.  (`RG/AnimalCount.lean`, ledger Add. 57.) | **code** — pure combinatorics, self-contained | **DONE** (core 8253) |
| **P1b** | **Spanning closed walk** (`exists_peel` + `exists_spanning_closed_walk`, `RG/AnimalTour.lean`, ledger Add. 59): an `S`-connected size-`n` set gets a closed walk from `r` of length `2(n−1)`, support `= S`, by peeling the farthest vertex and splicing with `exists_detour_walk`. | **code** — combinatorics, self-contained | **DONE** (core 8254) |
| **P1c** | **Lattice animal count** `animal_card_le` (`RG/AnimalTour.lean`, Add. 59): `A.card ≤ Δ^{2(n−1)}` for any family of `S`-connected size-`n` rooted sets — `c_n ≤ Cⁿ`, `C = Δ²` — via the injective `animal ↦ spanning walk` + P1a. | **code** — combinatorics | **DONE** (core 8254) |
| **P2a** | **`M`-cube adjacency graph + concrete summability** (`RG/CubeLattice.lean`, ledger Add. 61): `cubeAdj d L` (king-adjacency, Dimock II §3.1.2), `cubeAdj_degree_le` (`≤ 3^d`), `cube_polymer_summable` (`∑_Y q^{#Y} ≤ (1−(3^d)²q)⁻¹`).  Bulk / hole-free case. | code | **DONE** (core 8255) |
| **P2b-i** | **Holes / modified metric combinatorial core** (`walk_crosses_frontier` and `absorbedHole_touches_skeleton_single`, `RG/ModifiedMetric.lean`): the topological lemma for a walk crossing the frontier and the single-hole touching proof. | code — pure combinatorics | **DONE** (core 8264) |
| **P2b-ii-a** | **Holes multiplicity bounds and multi-hole combinatorics** (`absorbedHole_touches_skeleton_multi`, `touchingHoles_card_le`, and `card_le_activeEdges_add_one`, `RG/ModifiedMetric.lean`): the multi-hole skeleton-touching theorem, multiplicity bounds, and the active-edge cardinality bound. | code — combinatorics | **DONE** (core 8264) |
| **P2b-ii-b-1** | **Holes modified metric definition & skeleton card bound** (`discreteModifiedMetric`, `skeleton_card_le_discreteModifiedMetric_add_one`, and `discreteModifiedMetric_empty_holes`, `RG/ModifiedMetric.lean`): define the modified distance and prove the skeleton cardinality bound. | code — combinatorics | **DONE** (core 8264) |
| **P2b-ii-b-2** | **Multi-hole polymer fillings multiplicity bounds** (`admissibleFillings` and `fillings_card_le_two_pow`, `RG/ModifiedMetric.lean`): prove that the card of admissible fillings is bounded by $2^{\Delta \cdot |Y|}$. | code — combinatorics | **DONE** (core 8264) |
| **P2b-ii-b-3** | **Discrete metric comparison bounds** (`discreteModifiedMetric_le_bulkTreeLength`, `discreteModifiedMetric_mono_skeleton`, and `discreteModifiedMetric_mono_holes`, `RG/ModifiedMetric.lean`): prove comparison bounds with bulk tree length and monotonicity. | code — combinatorics | **DONE** (core 8264) |
| **P2b-ii-c** | **Skeleton-fillings weight summability** (`skeleton_fillings_weight_summable`, `RG/ModifiedMetric.lean`): preliminary combinatorial estimate showing that the skeleton-growth series converges under sufficient exponential metric decay. | code — combinatorics | **DONE** (core 8264) |
| **P2b-ii-d** | **Discrete modified-metric summability** (`discreteModifiedMetric_weight_summable`, `RG/ModifiedMetric.lean`): prove a volume-uniform summability theorem whose summand actually contains `discreteModifiedMetric H X` under coordination entropy-suppression. | code — combinatorics | **DONE** (core 8264) |
| **P2c** | **Type-local F.1 algebra and ultralocal independence** (`RG/LocalFunctional.lean`, `RG/RawMayerWithHoles.lean`, `RG/OmegaConnectedCover.lean`, `RG/UltralocalFactorization.lean`, `RG/MayerCoverFactorization.lean`): local activities, raw Mayer factors, Ω-connected cover products, factorwise-to-product support-containment lifting, product-measure factorization of disconnected fluctuation-support components, the finite disjoint-union integration split for Mayer-cover products, the fluctuation-overlap graph criterion turning no cross-edges into pairwise support disjointness, the finite confined-component split `K = I ∪ (K \ I)`, the all-components decomposition of `K` into disjoint confined components, the n-ary Mayer-cover integral factorization over those components, the constructor repackaging each confined Ω-overlap component as an `OmegaConnectedCover`, pairwise Ω-active support disjointness across distinct confined components, the canonical component-cover family partitioning exactly `K`, the graph-level support-containment adapter turning fluctuation-overlap edges into Ω-overlap edges, the support-inclusion bridge turning Ω-active components into ultralocal fluctuation factorization, and the cover-family product wrapper consumed by future F.1 source compilers. | code — finite algebra/measure theory | **DONE** (core 8283) |
| **P3** | **Cluster-expansion-with-holes convergence (Appendix F)**: the renormalized-activity decay `|H^#(Y)| ≤ O(1)H₀ e^{−(κ−3κ₀−3)d}` from the raw bound + summability.  Generalises `KP` convergence to the modified metric.  **The crux of (B).**  Source audit: Appendix F clusters are `Ω`-connected (`X₁ ∩ X₂ ∩ Ω ≠ ∅`), not ordinary full-polymer touching.  Use the new `omegaHolePolymerSystem` or prove a comparison theorem before reusing `holePolymerSystem` consumers. | code — HARD, months-scale | open (source §4) |
| **P4** | **Fluctuation integral → raw activity bound (§3.8)**: `|H_k(X)| ≤ H₀ e^{−κ d}` from the Gaussian step, `H₀ ∝ g_k^{κ₀}`.  **The crux of (A).** | code — HARD, months-scale, needs the lattice Gaussian covariance | open (source §4) |
| **P5** | **Assemble `hRpoly`**: combine P3 (renormalized decay) + P4 (raw bound) + P1/P2 (summability) ⟹ `|R_{t,k}| ≤ A e^{−c₀t} g_k^{κ₀}`; feed `lattice_mass_gap_of_cluster_and_coupling` ⟹ the **unconditional lattice mass gap**. | code (glue, once P1–P4 land) | open |

**Progress.**  The smallest non-vacuous first code brick (**P1a**, the
bounded-degree walk-count engine `≤ Δⁿ`) is **DONE** — `RG/AnimalCount.lean`,
oracle-clean, core 8253, ledger Add. 57.  It is pure combinatorics over
Mathlib's `SimpleGraph.finsetWalkLength`, needs no Bałaban/Dimock source,
and is the engine for the animal count.  **Next: P1b** — the animal count
`c_n ≤ Cⁿ` itself: build the cube-adjacency graph (degree bound from the
`M`-cube geometry), encode a connected size-`n` polymer as a length-`≤ 2n`
DFS walk rooted at the fixed cube (an injection), then
`Fintype.card_le_of_injective` against P1a gives `c_n ≤ (Δ)^{2n} = C ⁿ`
with `C = Δ²`.  The remaining genuine content is the **encoding injection**
(a connected set ↪ its canonical DFS walk); the count is then immediate
from P1a.  Consumer: `polymer_weight_summability` (closes branch C).

**P1b Mathlib reconnaissance + sub-ladder (design, 2026-06-13).**  Mathlib
*has* the tree predicates — `SimpleGraph.IsTree`, `IsAcyclic`,
`isTree_iff_existsUnique_path` (unique path between any two tree vertices),
`isTree_iff_minimal_connected`, `IsTree.card_edgeFinset` (`#E = #V − 1`) —
but **no Euler-tour / spanning-walk construction** (no "a tree on `m+1`
vertices has a closed walk of length `2m` visiting every vertex").  That
tour is the crux and must be built.  Honest sub-ladder:

* **P1b-i** — *spanning tree of a connected set*: from `G[S]` connected,
  obtain a tree subgraph spanning `S`.  Mathlib route: `Minimal Connected`
  /`Maximal IsAcyclic` (`isTree_iff_minimal_connected`,
  `maximal_isAcyclic_iff_isTree`) + extraction on the finite subgraph.
  Medium; reuses Mathlib.
* **P1b-ii** — *the tree Euler tour* (**the crux, not in Mathlib**): a
  finite tree on `m+1` vertices admits a closed walk from any root of
  length `2m` whose vertex support is all of `V`.  Build by induction on
  `#V` (peel a leaf — `IsTree` has a degree-1 vertex — splice its two
  tour-edges).  **Engine DONE** — `exists_detour_walk` (`RG/AnimalCount.lean`,
  ledger Add. 58): the inductive *step* (splice a `p→u→p` detour into a
  closed walk; length `+2`, support `+{u}`), oracle-clean.  Remaining: the
  leaf-induction *assembly* (iterate the engine over a spanning tree's
  leaves) — `IsTree.exists_vert_degree_one_of_nontrivial` +
  `Connected.induce_compl_singleton_of_degree_eq_one` supply the leaf-peel.
* **P1b-iii** — *the injection + count*: `S ↦ tour(S)` with `S` recovered
  as `(tour S).support.toFinset`, giving injectivity; then
  `Fintype.card_le_of_injective` into `{walks of length 2(n−1) from r}`
  and **P1a** (`card_walks_length_le_degree_pow`) yield
  `c_n ≤ Δ^{2(n−1)} ≤ (Δ²)ⁿ`.  Medium, given P1b-ii.

P1b-ii is a genuine standalone combinatorial development (no Mathlib
primitive); it — not a quick follow-on — is the real next working brick.

## 3bis. P3.5 sub-ladder — REGISTERED 2026-07-12 (before fabrication)

**Frontier re-audit finding (12-reader sweep + gap synthesis, 2026-07-12).**
The (642)-shaped renormalized-activity decay ALREADY exists as a composed
conditional theorem: `hraw` → K# at `appendixFKsharpRate κ κ₀ = κ−κ₀−2`
(`norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_canonicalRoot`)
→ weighted-tree/leaf summation → H# residual at
`polymerClusterResidualRate κ κ₀ = κ−3κ₀−3`
(`norm_appendixFHoleHsharp_le_residual_of_rawMetricDecay_canonicalRoot_halfBudget_of_source`)
→ `SingleScaleUVDecay` → marginal mass gap; (641) is proved three times and
consumed.  The connected-cover entropy estimate anticipated by §3/P3 is NOT
the missing brick.  What remains open, in order of size:

* **(O2)** no numeric witness anywhere that the parameter regime of the whole
  chain is non-empty (house rule 3 exposure);
* **(O3)** the carried cardinality-compression binder
  `(X.val.card : ℝ) ≤ θ·((d_M(X)+1 : ℕ) : ℝ)` is undischarged in
  `appendixFHoleTargetFiber_card_le_metricSum_of_source_card_le_metric`,
  `appendixFHoleMetricCoverWeight_mul_exp_card_le_shifted_of_source_card_le_metric`,
  `appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric`;
* **(O4)** the `hact` binder of
  `omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound`
  is not yet reachable from the H# lane (card-tilt composition);
* **(O5)** no end-to-end non-vacuity witness with NONZERO activities;
* **(O1)** the raw YM activity bound = hRpoly proper (months, unchanged).

**The ladder (each brick oracle-checkable, +1 job-count witness):**

| Brick | Module | Content | Kind | Status |
|---|---|---|---|---|
| **B1** | `RG/AppendixFParameterWitness.lean` | numeric κ₀(d), κ = 4κ₀+3, H₀ witnessing geometric smallness + leaf/root half-budget + the θ-extended budget for B3.  κ₀(d) = (3^d+1)log2 + 2d·log3 + 1 collapses the geometric product to EXACTLY e⁻¹; root ≤ 2, moment ≤ 2, leaf ≤ 16, H₀ = 1/256, half-budget margin ×2 | exp/log arithmetic | **DONE** (core 8386, ledger Add. 468) |
| **B2** | `RG/AppendixFHoleCompression.lean` | **bounded-hole cardinality compression** `X.card ≤ (1+3^d·B)·(d_M(X)+1)` for connected hole-respecting X with nonempty skeleton, holes of card ≤ B; discharges the (O3) binder verbatim with θ = 1+3^d·B; + no-holes exactness guard + concrete-hole strict witness | finite combinatorics | **DONE** (core 8385, ledger Add. 467) |
| **B3** | `RG/AppendixFHsharpCardTilt.lean` | H# residual + B2 + `appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric` + B1 θ-budget ⟹ the (O4) `hact` binder and the volume-uniform active-skeleton KP criterion (`appendixFHoleHsharp_tilted_majorant_of_residual_bounded_holes`, `omegaHolePolymerSystem_KPCriterion_of_Hsharp_residual_bounded_holes`) | composition | **DONE** (oracle-clean; dedicated B3 checkpoint) |
| **B4** | `RG/AppendixFEndToEndWitness.lean` | end-to-end instantiation at B1's parameters with a literally constant, strictly nonzero activity on the `d=1, L=1` torus; final active-skeleton KP criterion plus non-vacuity seal (`appendixF_endToEnd_nonzero_witness`) | witness | **DONE** (oracle-clean; dedicated B4 checkpoint) |
| **B5** | `RG/AppendixFHsharpRawToKP.lean` | compose the canonical-root raw-metric-decay theorem for the actual integrated `H#` activity with B3; removes the intermediate residual-`H#` caller hypothesis and reaches the active-skeleton KP criterion directly (`omegaHolePolymerSystem_KPCriterion_of_rawMetricDecay_canonicalRoot_boundedHoles`) | composition | **DONE** (oracle-clean; dedicated raw-to-KP checkpoint) |

**METHOD DEVIATION RECORDED (Trap C, C4-Amendment-1 style).**  The
unconditional compression `|X| ≤ θ(d_M(X)+1)` is FALSE — absorbed holes
inflate `X.card` at fixed skeleton.  Dimock pays the hole volume analytically
with the P4 Gaussian factor `e^{−c|H₀|}`; B2 pays with the uniform bound
`|H₀| ≤ B` as the honest finite-stage substitute.  When P4 lands, the `hB`
hypothesis must be revisited against the source's Gaussian payment; the
difference is on record here and in the module docstring.

**Registered traps (binding for B1–B4):** no terminal bound through
`appendixFHolePinnedMetricCoverSum` may be sold as (642) — pinning discards
`d_M(Y)` (Trap A); all new bricks stay on the `omegaHolePolymerSystem` side,
never the touching system (Trap B); `RawYMActivityDecay` must not be wired
directly to H# bypassing the fluctuation-integral structure (Trap D); filling
the free Prop slots of `AppendixFHsharpCluster3Contract` is zero content, not
a brick (Trap E).

## 3ter. P4-CT sub-ladder — REGISTERED 2026-07-12 (O1 attack, propagator-decay leg)

**Recon finding (2026-07-12, same session as §3bis).**  `KernelDecay.lean`
already proves the Neumann-series Combes–Thomas engine
(`expDecay_resolvent`, `finiteRange_resolvent_isExpDecay`) — but ONLY in the
small-hopping regime `M·e^{κR}·S < 1`.  The ACTUAL fixed-volume physical
precision operator (`flatGaugeHodgeK0 + a·Q†Q`, `GaugeFixedCovariance` lane)
is Laplacian-type: its invertibility is by COERCIVITY (block-Poincaré), not
entrywise smallness, and the existing engine cannot reach its inverse.  The
missing propagator-decay theorem of the O1/hRpoly statement is therefore:

**Weighted-conjugation Combes–Thomas for coercive finite-range lattice
operators** — for `K` self-adjoint coercive (`⟨f,Kf⟩ ≥ c‖f‖²`) with kernel
range `R` and entrywise bound `M` on a finite metric graph with shell
constant `N_R = max_x #{y : d x y ≤ R}`: for `θ` with
`M·(e^{θR}−1)·N_R ≤ c/2`,

`|K⁻¹(x,y)| ≤ (2/c)·e^{−θ·d(x,y)}`  (volume-uniform constants).

| Brick | Content | Kind | Status |
|---|---|---|---|
| **CT1** | tilt algebra (`physicalTiltCLM`/`physicalTiltConjCLM`, PhysicalCoerciveCombesThomas.lean): additive composition, conjugation identity, entry identity `e^{θ(dist r q − dist r p)}`, range preservation, tilted entry bound `M·e^{θR}` | finite algebra | **DONE** (core 8387, ledger Add. 469) |
| **CT2** | block Schur bound `‖A‖ ≤ β·N_R` (`physicalOpNorm_le_of_kernelBound_finiteRange`), perturbation bound `‖K_θ − K‖ ≤ M(e^{θR}−1)N_R`, coercivity survival `isCoerciveCLM_physicalTiltConj` | operator arithmetic | **DONE** (core 8387, ledger Add. 469) |
| **CT3** | tilted inverse: `K_θ` invertible with `‖K_θ⁻¹‖ ≤ (c/2)⁻¹ = 2/c` at the θ-budget `M(e^{θR}−1)N_R ≤ c/2`, via `covarianceOfIsCoerciveCLM` (`exists_physicalTiltConj_inverse_of_budget`, PhysicalCoerciveCombesThomasInverse.lean) | composition | **DONE** (core 8394, ledger Add. 475) |
| **CT4** | kernel extraction at root `r := source`: exact identity in two named halves (`physicalCovariance_entry_untilt` + `physicalTiltConj_tilted_probe`) ⟹ the headline `PhysicalCovarianceExponentialKernelBound C dist (2/c) θ` (`physicalCovariance_exponentialKernelBound_of_coercive`); instantiated at the flat physical shell: `flatGaugeFixedCovariance_CT_fixedVolume` + positive-rate `exists_flatGaugeFixedCovariance_CT_fixedVolume` (PhysicalShellCombesThomasEndpoint.lean) — the owner acceptance list (1)-(8) is CLOSED at fixed volume | composition + instantiation | **DONE** (core 8394, ledger Add. 475-476) |

**Non-vacuity obligations (binding):** CT4 must be instantiated on the
concrete flat physical shell with its PROVED finite stencils
(`fineLineSupport`/`linAvgSupport`/`flatBlockConstraintSupport`) and the
PROVED fixed-volume block-Poincaré constant — not on an abstract `K` chosen
to make the hypotheses easy.  CT4's fixed-volume statement says fixed-volume.

**W-1 — the volume-uniform Poincaré WALL: DONE, negative result (2026-07-13,
ledger Addendum 495, `PhysicalPoincareWall.lean`).**  The status of the
volume-uniformity of `c` is now FOUR distinct statements, none of which may
be conflated:
1. A volume-uniform POSITIVE Poincaré/coercivity theorem: **not proved**
   (and not claimed).
2. The uniform-constant gate for the CURRENT flat `linAvg` normalization
   (`VolumeUniformFlatPoincareGate`, constant quantified before the
   volume): **PROVED FALSE** for `d ≥ 3`, `Nc ≥ 2`
   (`volumeUniformFlatPoincareGate_false`; the wall is `L^d/L^2 ≤ CP`,
   hence `L ≤ CP`).
3. The current route to volume-uniform CT through `c = min 1 a / CP`:
   **CLOSED NEGATIVELY** (`no_volumeUniform_coercivity_via_flatPoincare`:
   any `c₀` dominated at every volume is `≤ 0`); the per-volume constants
   exist (`perVolume_flatPoincare_family`), so the dead route is real.
4. Registered continuations (in leverage order): harmonic/constant-sector
   quotient before the Poincaré step, rescaled block map (the wall must be
   re-audited there — it may merely move), or coercivity from the
   interacting Wilson Hessian directly.  `d = 2` is the scale-invariant
   exemption and is not covered by the wall.

**W-2 — the constant-sector quotient interface: DONE, result-neutral
(2026-07-13, ledger Addendum 499, `PhysicalPoincareSectorQuotient.lean`).**
Continuation (b) executed at the interface level: the constant sector
packaged as a linear inclusion (harmonic under the flat Hodge operator),
the fluctuation space as generator-wise orthogonality
(`IsFluctuationCochain`), the quotient(-interface) Poincaré predicate
`QuotientFlatGaugeHodgePoincare`, full → quotient at the same constant,
fixed-volume non-vacuity, and THE NON-TRANSFER LEMMA
(`constant_not_fluctuation`): the W-1 constant witness does not transfer
to the fluctuation space.  The volume-uniform QUOTIENT gate
(`VolumeUniformQuotientPoincareGate`) remains OPEN — neither proved nor
refuted; no claim in either direction is on record.  **W-3 (the
lowest-Fourier-mode falsifier) is ONE-SIDED**: it refutes the gate if the
low mode's Rayleigh quotient forces `CP → ∞` (a second wall); a bounded
quotient on that mode only removes one counter-witness candidate — proving
the gate additionally requires an all-fluctuation-modes estimate or a
spectral completeness/diagonalization theorem showing the studied mode
minimizes the quadratic form.  Formal precision (evaluator, on record):
no quotient TYPE or orthogonal-complement `Submodule` is constructed yet —
the predicate is a restriction to the fluctuation cochains; "quotient
interface" is the accurate name until the packaged subspace exists.

**W-3a/W-3b/W-3c — witness, exact Hodge term, and second wall: DONE
(2026-07-14, ledger Addenda 503/506/507).**  W-3a constructs the half-period
two-interface mode on the even torus `N = M + M`, proves exact orthogonality
to constants, exact norm `(M+M)^d * ‖w‖²`, genuine non-constancy, and
fluctuation-space non-vacuity.  W-3b (`PhysicalPoincareLowModeHodge.lean`)
evaluates its flat-Hodge energy exactly:
`⟪A,K₀A⟫ = 8 * (M+M)^(d-1) * ‖w‖²`.  The mechanism is explicit: `i = j`
has zero curl and all energy in divergence; `i ≠ j` has zero divergence and
all energy in the unique ordered `{i,j}` curl plane.  Hypotheses retained:
`d > 0`, `M > 0`, `Nc > 0`, even side; the identity itself needs neither
`Nc ≥ 2` nor `w ≠ 0`.  W-3c (`PhysicalPoincareLowModeBlock.lean`) resolves
the dependent side equality by canonical linear-isometric reindexing and
proves that constants, fluctuations, curl, divergence, norms, and Hodge
energy are preserved.  The current physical `Q` satisfies
`‖QA‖² ≤ L⁻¹‖A‖²` for `d ≥ 3`; combined with the exact Hodge ratio this
gives a Rayleigh numerator at most `9/L` times the norm and forces
`L/9 ≤ CP`.  Thus the ONE-SIDED falsifier fires:
`VolumeUniformQuotientPoincareGate` is false for every positive `N'`,
`d ≥ 3`, `Nc ≥ 2`.  This is the second wall for the current unscaled block
map and unweighted coarse norm; rescaled/weighted variants are different
gates and remain outside this theorem.

**OWNER CORRECTION ON RECORD (2026-07-12, post-CT1/CT2 review, BINDING).**
The CT1+CT2 checkpoint report overclaimed that "finite range + block bound +
coercivity are all three proved for the physical shell".  FALSE as stated:
only COERCIVITY is connected to `flatGaugeFixedPrecisionCLM` (block-Poincaré
route).  `PhysicalCovarianceFiniteRange` and the uniform
`PhysicalCovarianceKernelBound` are NOT yet proved for the concrete operator
`K₀ + a·Q†Q − Σᵢ Σᵢ`, whose `Sigma` family is arbitrary; the
`fineLineSupport`/`flatBlockConstraintSupport` stencils localize `K₀` and
`Q†Q` but NOT an arbitrary `∑ᵢ Sigmaᵢ`, and a norm bound `‖Sigmaᵢ‖ ≤ δᵢ` is
NOT locality.  Binding obligations for the CT3+locality+CT4 checkpoint
(owner, verbatim intent): (1) a CONCRETE `physicalBondDist` with symmetry,
triangle, `dist p p = 0`, and an explicit ball bound `N_R`; (2) term-by-term
`FiniteRange` + `KernelBound` for `flatGaugeHodgeK0CLM`, `a•Q†Q`, and the
`Sigma` term; (3) `Sigma` resolved honestly — free shell `Sigma = 0` named
as such (`zeroSigma`), or common range + summed kernel bounds, never
norm-as-locality; (4) CT3 at the budget `δ_θ = M(e^{θR}−1)N_R ≤ c/2` with
`0 < c − δ_θ` and `‖K_θ⁻¹‖ ≤ 2/c` explicit; (5) CT4 at root `r := source`
with the exact identity `K⁻¹δ_p(q) = e^{−θd(p,q)}·K_θ⁻¹δ_p(q)`; (6) endpoint
literally `PhysicalCovarianceExponentialKernelBound
(flatGaugeFixedCovarianceCLM …) physicalBondDist (2/c) θ`; (7) `0 < θ` with
a non-vacuous witness satisfying the CT budget at the physical constants;
(8) named `CT_fixedVolume`.  NOT accepted: abstract CT3 alone; `Sigma`
treated as local via norms; constant operator bounds sold as decay; `θ = 0`;
a certificate whose `hkernel` stays hypothetical; a fresh covariance not
identified with `flatGaugeFixedCovarianceCLM`.

**Honest scope:** CT1–CT4 deliver the propagator-decay leg of O1 for the
gauge-fixed FREE shell.  The interacting correction (G5 — the fluctuation
integral with small/large-field split surviving the interaction) remains the
wall, per `docs/UV-S2-GAUSSIAN-PLAN.md`.

**P4-ADJ (registered 2026-07-13, external-review finding).**
`SUNAdjointModel` had no constructed instance; the trivial witness
`trivialSUNAdjointModel` (adCLM g := id, exact for the flat lane where only
`adCLM 1` is consumed) and the full-chain audit `CT_fixedVolume_nonvacuous`
now close the NON-VACUITY half (`SUNAdjointModelWitness.lean`, ledger
Add. 477).  **DONE (2026-07-13, ledger Addenda 486/488/490/492): the TRUE
matricial adjoint model is `matrixSUNAdjointModel`**
(`SUNAdjointModelInstance.lean`) — `Ad(g)X = gXgᴴ` on traceless
skew-Hermitian matrices with the trace inner product
(`SUNAdjointMatrixSubstrate` + `SUNAdjointInnerSpace`), transported to
`EuclideanSpace ℝ (Fin (n²−1))` by the isometric basis identification
`suLieCoordIso` built on `finrank ℝ su(n) = n²−1`
(`SUNAdjointDimension`).  The trivial witness is no longer the only
instance.  Standing rule unchanged: the model becomes load-bearing the
moment the background is non-trivial (interacting lane); do not silently
substitute the trivial model there.

**External calibration on record (2026-07-13, ledger Add. 477).**  Reviewer
scale for the whole lane: fixed-volume free-shell CT = ~3.1/10 Clay
proximity (consistent with, and weaker than, hard rule 6's ~0%); the
recorded upgrade path: volume-uniform CT for the INTERACTING Wilson Hessian
+ root localization → 4–5; uniform interacting RG + lattice clustering/mass
gap → 6–7; continuum limit + QFT axioms → 8–9.

## 4. Source material — RECEIVED + corrections (2026-06-13)

The Dimock II/III page-level statements have now been provided and
cross-checked.  Corrections to earlier (second-hand) attributions, now
recorded in `BALABAN-SOURCE-BOUNDS.md` and ledger Add. 61:

1. **Appendix F is in Part II** (arXiv:1212.5562), and its convergence is
   self-contained there (it follows Part I App B) — **NOT** Part III.
   Theorem F.1: `H₀ ≤ c₀`, `κ ≥ 3κ₀+3`, hypothesis `|H(X)| ≤ H₀ e^{−κ d_M(X, mod Ω^c)}`,
   conclusion `|H^#(Y)| ≤ O(1)H₀ e^{−(κ−3κ₀−3) d_M(Y, mod Ω^c)}` — confirmed.
2. The `d_M(X, mod Ω^c)` definition + summability `∑_{X⊇□} e^{−κ₀ d_M} ≤ K₀`
   are in the **§3 main text (§3.1.2, eqs ~150–151)**, not Appendix F.
   `M`-cube adjacency = king-move (shared boundary of any dimension),
   coordination `3^d−1` — now formalized as `cubeAdj` (`RG/CubeLattice.lean`).
3. The raw activity bound is in **§3.14** (Lemma 3.18, eq. ~500/506:
   `|H_{k,Π}^+(Y)| ≤ O(1)L³ λ_k^{1/4−10ε} e^{−L(κ−3κ₀−3) d_{LM}(Y, mod Ω^c)}`),
   **not §3.8** (§3.8 = the fluctuation-integral / covariance-localization
   setup).  Coupling is **`λ_k`** (`= L^{−(N−k)}λ`), not `g_k`;
   `p_k = (−log λ_k)^p`, `α_k = max(λ_k^{1/4}, μ̄_k^{1/2})`; `H₀ ≍ O(1)L³ λ_k^{1/4−10ε}`.

**CRITICAL: Dimock II/III is `φ⁴₃` (3D scalar), not 4D Yang–Mills.**  App F
is a *general polymer lemma* reusable across models, but its constants
(`λ_k^{1/4−10ε}`, `L³`, the *relevant* coupling `λ_k = L^{−(N−k)}λ`) are
`φ⁴₃`-specific.  The 4D YM activity bounds and the (logarithmic, *marginal*)
YM coupling flow must come from Bałaban's YM papers — do NOT transcribe these
`φ⁴₃` numbers into the YM target.

Remaining genuinely-open analytic work (now source-grounded, still large):
**P3** (Appendix F cluster expansion with
holes, on top of the repo's KP layer), **P4** (the §3.14 raw activity bound,
which for YM needs the YM single-scale integral — not the `φ⁴₃` §3.14).

**Cluster-level substrate update (2026-06-19, Addenda 113–120).**  The
cluster-union interface now packages clusters as source-shaped hole polymers
(`clusterUnionPolymer`), controls their active skeleton by the cluster modified
metric, and proves the skeleton-pinned cluster remainder series bound
`clusterSkeletonRemainderSum_tsum_le`.  The follow-on consumer theorem
`clusterSkeletonRemainderSum_tsum_le_metric_bound` composes that KP estimate
with the discrete modified-metric summability theorem: an explicit
Dimock-shaped activity estimate
`exp(t) * ‖z(c)‖ * exp(|c|) ≤ A * q^(d_M(c)+1)` implies a volume-uniform
bound by `t⁻¹ * A * (1 - (3^d)^2 * (q * 2^(3^d+1)))⁻¹`.  The follow-up
`clusterSkeletonRemainderSum_tsum_le_metric_bound_of_local` derives the
needed tilted KP criterion from the local tilted activity-sum smallness
condition, using `holePolymerSystem_KPCriterion_volumeUniform_scaled`.  This
scaled local criterion also now feeds the tilted cluster-series convergence
and tilted norm-bound APIs, plus the local versions of raw-tail summability,
the quantitative raw-pinned bound, skeleton-tail summability, and the
pre-metric skeleton-pinned bound.  Addendum 120 names the
`ρ = exp(t)` specialization directly as
`holePolymerSystem_KPCriterion_volumeUniform_exp` and its convergence/norm
companions, so RG proofs can consume the source-shaped
`exp(t) * ‖z(Y)‖ * exp(|Y|)` local window without rebuilding scalar-norm
bookkeeping.  This does **not** prove the P3/P4 activity-decay theorem; it
proves the exact summability consumer interface that P3/P4 must feed.

**Appendix-F compatibility audit (2026-06-19).**  Direct source extraction
from Dimock II Appendix F confirms the with-holes cluster relation:
`Ω`-connected means `X₁ ∩ Ω` and `X₂ ∩ Ω` intersect, equivalently
`X₁ ∩ X₂ ∩ Ω ≠ ∅`; `Ω`-disjoint need not be disjoint.  The existing
`holePolymerSystem` remains the touching hard-core system supporting the
verified local-KP consumers, but it is not to be advertised as the literal
Appendix-F compatibility relation.  The new `omegaHolePolymerSystem`
uses nonempty active skeletons and incompatibility by skeleton intersection,
giving P3 a source-faithful entry point.  The follow-up source-facing local
KP package is now also theorem-fed:
`omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp` and its
convergence/norm companions show that a local window pinned at active skeleton
cubes is enough to run the KP convergence machinery for the literal
Appendix-F relation.  This still carries the model-specific activity estimate;
it closes the consumer side, not the Yang-Mills activity-decay theorem.  The
metric-bound bridge
`omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound`
now derives that local KP window from the source-shaped pointwise estimate
`exp(t)‖z(Y)‖exp(|Y|) ≤ A q^(d_M(Y)+1)` plus the discrete modified-metric
summability already proved in P2b.  Its direct convergence and norm-bound
companions package the same metric-bound hypotheses all the way to the
active-system Mayer cluster series.
The active relation now also has a cluster-tail consumer:
`omegaClusterSkeletonRemainderSum_tsum_le_metric_bound` defines the
Appendix-F-facing skeleton-pinned remainder term and bounds its `tsum` by
`t⁻¹ A (1 - (3^d)^2(q 2^(3^d+1)))⁻¹` under the same pointwise
modified-metric activity majorant.  Thus future P3/P4 work can feed the
literal `Ω`-connected relation without detouring through the older touching
hard-core system.
The same active cluster-tail path also has local-window consumers
`omegaClusterSkeletonRemainderSum_summable_of_local` and
`omegaClusterSkeletonRemainderSum_tsum_le_of_local`: if a primary source gives
the activity estimate as a local active-skeleton polymer norm rather than a
literal pointwise metric majorant, the repo can consume that form directly.
The uniform local-window variants
`omegaClusterSkeletonRemainderSum_summable_of_uniform_local` and
`omegaClusterSkeletonRemainderSum_tsum_le_of_uniform_local` package the common
source form `local active-skeleton norm ≤ B ≤ 1`, yielding the tail bound
`≤ t⁻¹ B` without exposing the root-pinned finite sum in downstream statements.

**Finite target-gas checkpoint (2026-06-20).**  The single-support
Appendix-F compiler has the exact finite Fubini/lumping bridge from
admissible connected-cover families to admissible target families with fiber
activities `K(Y)`.  The source-faithful with-holes adapter is now also
theorem-fed for `omegaHolePolymerSystem`: `AppendixFHoleTarget.lean` proves
that `skeleton (⋃ X_i) = ⋃ skeleton(X_i)`, every representable full target is a
valid active hole-polymer, and the full-target union map is
injective/cardinality-preserving on admissible connected-cover families even
though admissibility uses only active-skeleton disjointness.  The follow-up
module `AppendixFHoleTargetFamily.lean` closes the corresponding two-support
target-choice Fubini/lumping identity, with active support
`skeleton HF X.val` and target support `X.val`: target choices are reindexed by
connected-cover families, the product over full-target fiber activities equals
the connected-cover family sum, and the finite raw Mayer product is recovered
as `prod_one_add_eq_sum_appendixFHoleAdmissibleTargetFamilies` (plus
`complex_exp_sum_eq_sum_appendixFHoleAdmissibleTargetFamilies`).  The remaining
Appendix-F work is now analytic/geometric rather than this finite lumping
step: connected-cover entropy/activity bound (642), integration to `K#`,
second Ursell expansion to `H#`, and the source-specific raw Yang-Mills
activity estimate.  The finite metric stitching item is closed below.

**Finite first-activity quantitative checkpoint (2026-06-20).**
`AppendixFQuantitative.lean` adds the first source-independent quantitative
layer above that compiler.  If each raw activity satisfies
`‖h X‖ ≤ H0 * exp(-κ * metric X)` with `0 ≤ H0 ≤ 1` and `0 ≤ κ`, then
`norm_appendixFConnectedActivity_le_metricCoverSum` bounds the first connected
activity `K(Y)` by the explicit finite connected-cover sum
`Σ_C (2H0)^{|C|} exp(-κ Σ_{X∈C} metric X)`.  The source-facing theorem
`norm_appendixFHoleConnectedMayerActivity_expSubOne_le_metricCoverSum`
specializes this to `omegaHolePolymerSystem`, using active skeletons for
connectivity and full hole-polymer unions for targets.  This is not yet the
full Dimock (641)--(642): the remaining P3 work is to combine finite metric
stitching with connected-cover entropy to control that sum by the modified
metric of the target `Y`, then integrate to `K#` and run the second
Ursell/logarithmic expansion to `H#`.
The finite localization bridge is now also theorem-fed:
`norm_appendixFHoleConnectedMayerActivity_expSubOne_le_pinnedMetricCoverSum`
shows that, for any `r ∈ Y`, the same first activity is bounded by the pinned
connected-cover sum over covers containing some raw full polymer through `r`.
This is the source-facing local-influence form needed before applying a
Dimock-style entropy/metric estimate; it deliberately leaves that pinned sum
unestimated.

The finite with-holes modified-metric stitching is also theorem-fed:
`appendixFHoleTargetFiber_discreteModifiedMetric_add_one_le_sum` proves that
every active-skeleton connected target-fiber cover satisfies
`d_M(Y, mod holes)+1 ≤ Σ_X (d_M(X, mod holes)+1)`, using the repository's
`discreteModifiedMetric` and the active-skeleton/full-target split.  This is
the geometric part of Dimock's (641).  It still leaves the connected-cover
entropy estimate and the final activity bound (642) open.

### P4 route refinement: collar factorization from covariance decay

Lluis Eriksson's outlook paper
`The Heisenberg Cut as a Resource Boundary` (`ai.vixra:2512.0064v1`) should not
be imported literally into `YangMillsCore`: its thermodynamic power,
battery-assisted operations, Heisenberg-cut interpretation, and Type-III
maintenance discussion are a different physical programme.  The useful
mathematical idea is narrower and source-compatible:

`auxiliary RG spectral mass / coercivity → ExpDecay covariance → collar
suppression → local decoupling`.

The first theorem from this route is now in `KernelSchur.lean`:
`expDecay_separated_finset_sum_le`.  If `|K i j| ≤ a exp(-κ d(i,j))` and two
finite regions are separated by a collar `ε`, then

`Σ_{i∈A,j∈B} |K i j| L_i M_j ≤ a exp(-κ ε) (Σ_i L_i)(Σ_j M_j)`.

This is the deterministic algebraic core that a future Gaussian interpolation
proof will consume after integration by parts supplies the derivative weights.
It does not prove the Yang-Mills fluctuation-integral activity bound; it
removes one clean finite-sum step between covariance decay and polymer
decoupling.

The same block-1 audit also identifies a separate, local large-field cutoff
dictionary: Bałaban's analytic logarithmic coordinate must be compared to the
geometric group deviation through `Y = D - 1`, not through `D` itself.  This is
now a verified near-identity theorem in `NearLog.lean`:
`norm_nearLog_two_sided_of_norm_le_third`, namely

`‖Y‖ ≤ 1/3 → ‖Y‖ ≤ 2‖nearLog Y‖ ∧ ‖nearLog Y‖ ≤ 2‖Y‖`.

This is a **green** local cutoff-conversion brick.  The much stronger claim
that a conditioned fast-field measure is literally Bałaban's `T`-operation
remains an **amber/dark** interface until the disintegration and density
comparison are reconstructed from the primary Bałaban source.

The later paper audit also sharpens a potentially shorter covariance route:
the scalar UV assembly consumes a terminal decay estimate, so some of the full
renormalized-activity machinery may be bypassable if one can prove the needed
single-scale covariance/influence decay directly.  The first safe Lean brick
of that route is now in `AveragingAdjoint.lean`: the scaled Hilbert-space
averaging map `scaledLinAvgCLM` on bond `ℓ²`/`PiLp 2` spaces and its adjoint
mass `qMassCLM = Q†Q`, with the energy identity, positivity, and
`‖Q†Q‖ ≤ ‖Q‖²`.  The scalar normalization is deliberately left as `s : ℝ`.
This is only the deterministic mass algebra for a future Gaussian block
kernel; the finite-range kernel, Hessian coercivity, influence matrix, and
activity-decay theorem remain open.

A separate SUSY-style audit is recorded in
`docs/SUSY-HRPOLY-ACCELERATION-PLAN.md`.  It does **not** add a supersymmetric
physical theory to the Clay target.  Its useful content is an abstract
cohomological cancellation layer: decompose local activities as `H = Q B + R`,
use an exact or approximate Ward identity to kill the `Q`-exact part before
norming, and feed the remaining scalar profile to the existing with-holes KP
consumers.  The opening substrate is `YangMills/SUSY/WardComplex.lean`, plus
the regulator-limit bridge `YangMills/RG/ActivityLimit.lean`.
The regulator bridge now includes the telescopic form
`activity_profile_bound_of_tendsto_telescope`: a pointwise regulator sequence
with initial amplitude `amp` and summable profile-weighted increments of total
budget `S` passes to a limiting activity with amplitude `amp + S`.
The next bridge is now also theorem-fed in `YangMills/SUSY/WardPolymer.lean`:
an exact or approximate Ward decomposition of the raw activity produces the
literal pointwise modified-metric hypothesis consumed by
`omegaClusterSkeletonRemainderSum_tsum_le_metric_bound`.  This closes the
consumer side of the Ward route; the model-specific decomposition, regulator
defect estimate, primitive bound, and cohomological remainder bound remain
open.

The kinetic-sweep audit also recommended separating the final scalar consumer
from its possible producers.  This is now theorem-fed in
`YangMills/RG/SingleScaleUVDecay.lean`:

* `SingleScaleUVDecay` is the scalar per-scale estimate consumed by
  `UVMassGap`;
* `RawYMActivityDecay` names the pre-renormalized fluctuation-integral profile;
* `RenormalizedHoleActivityDecay` names the Appendix-F with-holes output
  profile;
* `singleScaleUVDecay_of_renormalizedHoleActivities` proves the actual
  summation bridge from renormalized activities plus `∑ w ≤ K₀` to scalar
  `SingleScaleUVDecay`.

This permits parallel producers such as Appendix F, direct covariance, or Ward
cancellation to target the same scalar interface without relabelling their
unproved analytic inputs.

The first constructive F.1 substrate is now `YangMills/RG/LocalFunctional.lean`.
It follows the "locality in the types" design: a `LocalFunctional` can only
evaluate a `RestrictedField` on its finite support, and a two-field
`LocalActivity` has separate spectator/fluctuation supports.  The global
adapters satisfy oracle-clean invariance theorems under changes off support,
and finite products automatically carry the union of supports.  This is the
typed locality layer that the next F.1 constructions should consume; it is not
Appendix F itself.

The ultralocal independence substrate is now
`YangMills/RG/UltralocalFactorization.lean`.  It proves that two
`LocalFunctional`s with disjoint supports factorize under an explicit finite
product probability measure, and that two `LocalActivity`s with disjoint
fluctuation supports factorize for a fixed spectator field.  This is the
finite product-measure step needed by future fluctuation-integral compilers;
it is not the Gaussian covariance estimate, not the Appendix-F polymer loss,
and not the Yang-Mills activity-decay theorem.

The raw local Mayer step is now in `YangMills/RG/RawMayerWithHoles.lean`.  It
defines `rawMayer` on both `LocalFunctional` and two-field `LocalActivity` as
`H ↦ exp H - 1`, preserving supports by construction, inheriting the
off-support invariance theorem, and proving the elementary small-activity
bound `‖exp z - 1‖ ≤ 2‖z‖` under `‖z‖ ≤ 1`.  This is the local `H_X ↦ m_X`
map of the future Dimock-F.1 compiler, not the Ω-connected cover, not
ultralocal integration, and not the Yang-Mills activity-decay estimate.

The next source-shaped cover substrate is now in
`YangMills/RG/OmegaConnectedCover.lean`.  It defines the Ω-overlap graph on
cover indices, the predicate/structure carrying Ω-connectedness, and the
finite Mayer-cover activity `∏ᵢ (exp Hᵢ - 1)` as a type-local `LocalActivity`.
The spectator and fluctuation supports are exactly the unions of the supports
of the factors, and global evaluation is the product of the raw Mayer factors.
This is still algebraic F.1 scaffolding: it records the combinatorial
Ω-connected cover and product locality, but it does not perform ultralocal
integration, prove the Appendix-F polymer loss, or establish the Yang-Mills
activity-decay bound.

The disconnected-cover compiler now has a graph-level handoff in
`YangMills/RG/MayerCoverFactorization.lean`: `fluctuationOverlapGraph` records
overlap of activity fluctuation supports, and
`mayerCoverActivity_union_integral_of_no_cross_fluctuationAdj` proves that two
disjoint index blocks with no cross-edge in that graph satisfy the finite
Mayer-cover integral split.  This is still finite algebra plus product-measure
independence; it does not identify the source-specific Appendix-F components
or prove any quantitative polymer loss.

The same module also defines `confinedComponent G K r`, the finite component
of a root inside a cover index set using only walks whose support remains in
`K`.  The theorem
`mayerCoverActivity_integral_split_confinedComponent` packages the automatic
split of `K` into that component and its complement under the
fluctuation-overlap graph.  This is the component-extraction producer for the
no-cross-edge theorem above.

The finite all-components layer is now explicit as `confinedComponents G K`.
It proves `(confinedComponents G K).biUnion id = K`, that intersecting
confined components are equal, and hence that distinct confined components are
disjoint.  This is still the finite compiler substrate only: it prepares the
n-ary component factorization over a Mayer cover, but it does not prove
Dimock Appendix F, source-specific activity decay, or any continuum statement.

That n-ary finite factorization is now also theorem-fed:
`mayerCoverActivity_biUnion_integral_of_no_cross_components` proves the
generic product formula over a finite family of pairwise disjoint blocks with no
cross-edge in the fluctuation-overlap graph, and
`mayerCoverActivity_integral_factor_confinedComponents` instantiates it for the
confined-component partition of a cover `K`.  This removes the need to iterate
the binary root/complement split by hand in future finite F.1 compiler work.

The component partition now also connects back to the source-shaped Ω-cover
API.  `confinedComponent_walkConnected` proves that a confined component is
walk-connected in the ambient graph, and
`OmegaConnectedCover.confinedComponentCover` packages a confined component of
the Ω-overlap graph as an `OmegaConnectedCover` with the same index set,
Ω-region, and active-support map.  The theorem
`exists_confinedComponentCover_of_mem_confinedComponents` lifts every member
of `confinedComponents (omegaOverlapGraph Ω activeSupport) K` to such a cover.
This is still finite compiler algebra: it supplies the handoff from
disconnected component extraction to the existing Ω-connected Mayer-product
API, not the analytic Appendix-F activity estimate.

For distinct confined components of the Ω-overlap graph,
`omegaActiveSupport_disjoint_of_mem_confinedComponents_ne` and its pairwise
wrapper convert the graph separation back to the source-facing statement
`Disjoint (Ω ∩ activeSupport i) (Ω ∩ activeSupport j)` across component
indices.  This is the exact finite separation fact a later Appendix-F compiler
needs before applying any model-specific activity estimate.

The canonical family interface is now also theorem-fed:
`confinedComponentCoverOfComponent` chooses an `OmegaConnectedCover` for a
known member of `confinedComponents`, `confinedComponentCoverFamily` indexes
these covers by the subtype of components, and
`biUnion_confinedComponentCoverFamily_index_eq` proves that the union of the
family's cover indices is exactly the original finite set `K`.  The companion
`pairwise_omegaActiveSupport_disjoint_confinedComponentCoverFamily` packages
the pairwise Ω-active separation directly at the cover-family level.
The index partition itself is explicit:
`disjoint_confinedComponentCoverFamily_index_of_ne` and
`pairwise_disjoint_confinedComponentCoverFamily_index` prove that distinct
entries of this family have disjoint index sets.
The source-to-measure bridge is also explicit:
`LocalActivity.mayerCoverActivity_fluctuationSupport_subset_omega_biUnion_activeSupport`
and
`OmegaConnectedCover.mayerActivity_fluctuationSupport_subset_omega_biUnion_activeSupport`
lift factorwise containment
`(H i).fluctuationSupport ⊆ Ω ∩ activeSupport i` to the corresponding
Mayer-cover product support containment inside the union of declared active
supports.
The same source-facing product API now has a pointwise quantitative bound:
`LocalActivity.norm_globalEval_mayerCoverActivity_le_prod_two_of_norm_le` and
`OmegaConnectedCover.norm_globalEval_mayerActivity_le_prod_two_of_norm_le`
show that factorwise raw estimates `‖Hᵢ‖ ≤ Aᵢ ≤ 1` imply
`‖∏ᵢ (exp Hᵢ - 1)‖ ≤ ∏ᵢ 2Aᵢ`.
The uniform-amplitude forms
`LocalActivity.norm_globalEval_mayerCoverActivity_le_two_mul_pow_card_of_norm_le`
and
`OmegaConnectedCover.norm_globalEval_mayerActivity_le_two_mul_pow_card_of_norm_le`
specialize this to the source-common profile
`‖∏ᵢ (exp Hᵢ - 1)‖ ≤ (2A)^{|I|}`.
The decay forms
`LocalActivity.norm_globalEval_mayerCoverActivity_le_two_mul_pow_of_le_card`
and
`OmegaConnectedCover.norm_globalEval_mayerActivity_le_two_mul_pow_of_le_card`
then turn any source-proved lower bound `n ≤ |I|` into
`‖∏ᵢ (exp Hᵢ - 1)‖ ≤ (2A)^n`, provided `2A ≤ 1`.
`LocalActivity.fluctuationOverlapGraph_adj_imp_omegaOverlapGraph_adj_of_fluctuationSupport_subset`
proves the graph-level adapter: if each local fluctuation support is contained
in its declared `Ω ∩ activeSupport i`, then every actual fluctuation-overlap
edge is an Ω-overlap edge.
`LocalActivity.mayerCoverActivity_integral_factor_confinedOmegaComponents_of_fluctuationSupport_subset`
proves that the confined Ω-overlap components factorize the ultralocal
fluctuation integral whenever each local fluctuation support is contained in
its declared `Ω ∩ activeSupport i`.
The cover-family-facing wrapper
`OmegaConnectedCover.mayerActivity_integral_factor_confinedComponentCoverFamily_of_fluctuationSupport_subset`
rewrites the product directly over `confinedComponentCoverFamily`, so later
source compilers do not need to unfold raw component finsets.

(Historical note: the request below is satisfied; kept for provenance.)
All three PDFs (1108.1335, 1212.5562, 1304.0705) are uploaded; the
request was for the **specific page-level theorem statements** so the Lean
constants are read off the page, not reconstructed (per the Opus
miscalibration warning recorded in `BALABAN-SOURCE-BOUNDS.md` §2).

## 5. Honest difficulty + Clay scope

P1 is tractable (combinatorics).  **P3 and P4 are the genuine
months-scale cores** — the cluster expansion with holes and the
fluctuation integral — for which Mathlib has no primitives (no polymer
animal model, no lattice Gaussian covariance operator with Combes–Thomas
decay).  Even a full P1–P5 discharge yields only the **lattice** (M3)
mass gap; M4 (continuum limit) and M5 (OS/Wightman reconstruction) remain
untouched open mathematics.  **Distance to the Clay prize: ~0% (<0.1%),
unchanged** — and every status document is required to say so.
