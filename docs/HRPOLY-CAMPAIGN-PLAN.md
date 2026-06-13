# `hRpoly` CAMPAIGN — the cluster-expansion-with-holes activity bound

**Date:** 2026-06-12.  **Status:** P0 (design / source-grounding).  This
is a **design + source-transcription** document (no Lean proved here),
per the campaign rules.  It opens the months-scale campaign to discharge
`hRpoly`, the **sole remaining genuinely-analytic carried input** of the
end-to-end UV conditional `lattice_mass_gap_of_cluster_and_coupling`
(`RG/UVMassGap.lean`).

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
`∑_Y q^{#Y} ≤ (1−Δ²q)⁻¹` for `Δ²q < 1`.  Remaining: the **P2 instantiation**
(identify Dimock `M`-cube polymers with rooted connected sets, `q = e^{−κ₀}`).

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
| **P2** | **Polymer-with-holes model**: the polymer type (connected `M`-cube unions), the modified distance `d_M(·, mod Ω^c)`, the `KP.PolymerSystem` instance / bridge, and the **interface task** of feeding `animal_card_le` (P1c) into `polymer_weight_summability` (`hcount`).  Define + non-vacuity. | code (definitional, with P1/P3 consumers) | **next** |
| **P3** | **Cluster-expansion-with-holes convergence (Appendix F)**: the renormalized-activity decay `|H^#(Y)| ≤ O(1)H₀ e^{−(κ−3κ₀−3)d}` from the raw bound + summability.  Generalises `KP` convergence to the modified metric.  **The crux of (B).** | code — HARD, months-scale | open (source §4) |
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

## 4. Precise source material requested (for P3, P4)

To build P3/P4 non-vacuously (not a faked interface), I need the
**verbatim statements with exact constants** — the transcriptions in
`BALABAN-SOURCE-BOUNDS.md` are second-hand and the constants are flagged:

1. **Dimock II, arXiv:1212.5562, Appendix F** — the cluster-expansion-
   with-holes theorem: the exact hypotheses (`H₀ ≤ c₀`, the relation
   `κ ≥ 3κ₀+3`), the exact conclusion (`|H^#(Y)| ≤ O(1)H₀ e^{−(κ−3κ₀−3)d}`),
   the definition of `d_M(X, mod Ω^c)`, and the `∘`-product/polymer
   conventions.  **Confirm whether the convergence with the summable
   conclusion is in Part II App F or in Part III (arXiv:1304.0705)** — the
   convergence is deferred to Part III in Part II's front matter.
2. **Dimock §3.8** (Part I arXiv:1108.1335 small-field, or Part II) — the
   explicit fluctuation integral: the covariance `C_{k,Ω}`, the change of
   variables to the local field `W_k`, and the resulting **raw activity
   bound** `|H_k(X)| ≤ H₀ e^{−κ d_M(X)}` with `H₀` in terms of `g_k`,
   `p_k = (−log λ_k)^p`, `α_k`.
3. (P1, optional) the exact **polymer/`M`-cube adjacency** and the
   `d_M(·, mod Ω^c)` definition, so the animal-count constant `C` is
   faithful to Dimock's geometry.

All three PDFs (1108.1335, 1212.5562, 1304.0705) are uploaded; the
request is for the **specific page-level theorem statements** so the Lean
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
