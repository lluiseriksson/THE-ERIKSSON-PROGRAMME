# AREA-LAW PLAN (T4, the Wilson-loop form)

**Date:** 2026-06-11.  **Status:** strategic design, post-audit.  No
Lean code in this document.

**Target:** the strong-coupling area law for the fundamental Wilson
loop on the SU(N_c) lattice gauge theory:

    |⟨W_C⟩| ≤ C₀ · r^{Area(C)},   r = r(β, N_c) < 1 at small β,

where `W_C(A) = Re tr (wilsonLine A C)` and `Area(C)` is the minimal
number of plaquettes spanning `C`.

---

## 1. The post-shortcut strategic picture

`PETER_WEYL_ROADMAP.md` (2026-04-19) routed ALL of T4 through
Peter–Weyl → Schur → character expansion → KP.  Since then:

* the KP layer (its L4) is **done**, in a stronger volume-uniform
  form than the roadmap asked for (the entire cluster-correlation
  campaign, `docs/CLUSTER-CORRELATION-PLAN.md`);
* the two-plaquette correlator decay (its L4.4 endpoint) is **done
  without Peter–Weyl** (`two_plaquette_correlator_bound`, the
  singleton-support shortcut);
* the Schur/selection-rule layer (its L2) is **done at the moment
  level**: `SchurMomentVanishing`, `SchurMixedMomentVanishing`,
  `SchurPowerSumVanishing`, `SchurMixedPowerSumVanishing`,
  `SchurEntryNAlitySelection`, `GaugeEdgeExpectation`
  (single-edge/two-edge/mixed-power trace integrals vanish off
  balance), `SchurEntryOrthogonality`, `CenterVanishing`.

**Key audit finding:** the area law does NOT need the Peter–Weyl
decomposition either.  What it needs per edge is the **balance
criterion** — `∫ (entries of U)^{⊗a} ⊗ (entries of U†)^{⊗b} dHaar = 0
unless the N-ality balances` — which is exactly the selection-rule
machinery already in the core, not the full `L²(G)` decomposition.
Peter–Weyl remains the route to SHARP constants and the character
expansion's all-order bookkeeping, but the leading-order area law at
small β is reachable with banked assets plus new combinatorics.

## 2. The route

Expand `⟨W_C⟩·Z = ∫ W_C · ∏_p (1 + f_p)` (binomial,
`weightedPartition_eq_sum`-pattern):

    ⟨W_C⟩·Z = ∑_{S ⊆ plaquettes} ∫ W_C · ∏_{p∈S} f_p.

Per term, the integral factorizes over the product measure
edge-by-edge (the `integral_mul_of_disjoint_deps` engine).  Each edge
`e` carries: one factor from `W_C` if `e ∈ C`, and one factor from
each `p ∈ S` with `e ∈ supp p`.

* **(A) Edge-balance vanishing:** if some edge of `C` is touched by
  NO plaquette of `S` (or more generally the per-edge N-ality doesn't
  balance), the per-edge Haar integral vanishes — the term dies.
  Status: trace-level instances banked (`GaugeEdgeExpectation`); the
  general entry-level statement needed here is a finite family of
  Weingarten-degree-(0,1,2) facts, NOT general Weingarten calculus.
* **(B) Surface bound:** any `S` whose plaquettes cover every edge of
  `C` with balanced N-ality contains a spanning surface, hence
  `|S| ≥ Area(C)`.  Status: NEW — discrete surface combinatorics
  (`ℤ`-chain/boundary argument: `∂(∑_{p∈S} ±p) = C` forces
  `|S| ≥ Area`).  This is the genuinely novel formal content.
* **(C) Per-term bound + entropy:** `|∫ W_C ∏_S f_p| ≤ N_c·δ_w^{|S|}`
  (boundedness, banked) and the sum over `S ⊇ a spanning structure`
  is controlled by the lattice-animal entropy already banked
  (`card_connectedPolymers_le`, `sum_connectedPolymers_through_le`)
  plus the geometric tail — the same `x/(1−Kx)` pattern as the
  correlator campaign.
* **(D) Normalization:** divide by `Z = exp(K) ≠ 0` (banked) or run
  the division-free form as in `truncated_correlation_bound`.

## 3. Brick ladder (estimated)

| Brick | Content | New? | Est. effort |
|---|---|---|---|
| AL1 | `ℤ`-chain complex on the lattice: plaquette boundary map `∂₂`, edge boundary `∂₁`, `∂₁∘∂₂ = 0` — **CLOSED** (commit `ad58393`, `L0_Lattice/ChainComplex.lean`, oracle clean; abstract over `FiniteLatticeGeometry`, whose `plaquetteEdge_src/dst` axioms ARE the closure of the square; Fintype class-fields bound via `letI`, the `WilsonAction` pattern) | done | — |
| AL2 | `Area(C) :=` min `|S|` with `∂₂S = C` — **CLOSED** (commit `7144e77`: `chainSupport`, `chainArea` (`sInf`), `chainArea_le`, `exists_minimal_spanning`, `chainBoundary₁_eq_zero_of_spans`; oracle clean).  **Ring-generic since `9f3c322`:** the whole AL1/AL2 theory now lives over an arbitrary `CommRing R` — `R := ℤ` for the integral theory, `R := ZMod N_c` for the `N`-ality theory AL5 needs.  No `ZMod`-descent lemmas required: just instantiate. | done | — |
| AL3 | entry-level edge-balance vanishing — **CLOSED BY AUDIT (2026-06-11): already banked.** `sunHaarProb_fundMonomial_integral_zero` (`ClayCore/SchurEntryNAlitySelection.lean`) IS the per-edge balance criterion: `∫ (∏ U_{iₛjₛ})·(∏ conj U_{kₜlₜ}) dHaar = 0` whenever `N_c ∤ (n−m)` — in particular for an uncovered loop edge (`n−m = ±1`, any `N_c ≥ 2`).  Peter–Weyl-free (centre element + Haar invariance).  For the SURVIVING balanced terms AL4 may additionally use `SchurEntryOrthogonality` (the `(1,1)` pairing `δδ/N`).  **Refinement for AL5:** since vanishing is governed mod `N_c`, the spanning argument should run in the chain complex over `ℤ/N_c` (trivial descent of AL1/AL2); the resulting bound is the `N`-ality area — the correct object for fundamental loops. | banked | — |
| AL4 | factorized expansion of `⟨W_C⟩·Z` with per-edge integration (the `WeightedGas` engine + AL3).  **Substrate CLOSED:** `L1_GibbsMeasure/EdgeFactorization.lean` — `integral_mul_of_disjoint_deps_complex` (the `ℂ`-valued two-block independence factorization, twin of the ℝ engine) and `integral_single_coord_marginal` (single-coordinate split-off `∫F₀(x e₀)·F₁ = ∫F₀·∫F₁`, the per-edge integration step; iterate over edges).  Oracle clean.  House note: at `ℂ` the bare `rw [integral_prod_mul]` fails on hidden instance arguments even when pattern and target PRINT identically — compose in term mode (`hmul.trans (congrArg₂ (·*·) h1F.symm h1G.symm)`); defeq checking succeeds where keyed matching fails.  **Binomial expansion CLOSED:** `L1_GibbsMeasure/WilsonLoopExpansion.lean` — `integral_mul_prod_one_add`: `∫ W·∏_p(1+f_p) = ∑_{S⊆t} ∫ W·∏_{p∈S} f_p` for bounded measurable `ℂ`-valued observables under a probability measure (via `Finset.prod_one_add` + `Integrable.bdd_mul` + `integral_finset_sum`).  Oracle clean.  Remaining: per-edge monomial bookkeeping wiring the expansion terms into AL3's balance criterion (W_C and f_p as products of edge-entry monomials, then `integral_single_coord_marginal` per edge). | mostly done | 1 session |
| AL5 | the spanning-surface lower bound (AL1+AL2 ⇒ nonzero terms have `|S| ≥ Area`).  **Interface CLOSED:** `chainArea_le_card_of_support_subset` (spanning chain supported in `S` ⇒ `Area ≤ |S|`) + `indicatorChain`/`chainSupport_indicatorChain_subset` (the restriction chain a non-vanishing term carries), in `ChainComplex.lean`, oracle clean.  The ring-generic AL2 absorbed the substance; what remains of AL5 is producing the balanced chain FROM the non-vanishing of a term — which is AL4's monomial bookkeeping, the campaign's one open brick. | interface done | folded into AL4 |
| AL6 | entropy + tail ⇒ `|⟨W_C⟩| ≤ C₀·r^{Area}`; non-vacuity window | banked patterns | 1 session |

Total: a 6–10 session campaign — smaller than the roadmap's
Peter–Weyl path (its L1 alone was 2500–5000 LOC, HIGH risk), with the
single high-novelty item being AL1/AL5 (discrete surface theory).

## 4. The join brick (AL4.5): from non-vanishing terms to balanced chains

The one open brick (2026-06-11 design).  Everything else is banked:
the expansion (`integral_mul_prod_one_add`), the per-edge split-off
(`integral_single_coord_marginal`), the balance criterion
(`sunHaarProb_fundMonomial_integral_zero`), and the area interface
(`chainArea_le_card_of_support_subset` + `indicatorChain`).

**Route (the one-unbalanced-edge shortcut).**  Do NOT build the full
per-edge product factorization.  To kill a term it suffices to
exhibit ONE unbalanced edge:

1. **Trace expansion (TE):** `tr(∏_{i<L} U_i) = ∑_{k : Fin L → Fin N_c}
   ∏_i (U_i)_{k i, k (i+1)}` — induction on `L` via `Matrix.mul_apply`.
   Applied to `W_C` and to each `f_p` (taken in the linearized class:
   `f_p` a `ℂ`-combination of degree-`(1,0)` and `(0,1)` monomials in
   its four edge matrices — `tr U_p` and `conj tr U_p` terms).  After
   full expansion, `T_S = ∑_terms ∫ ∏_{e} (fundMonomial of degree
   (n_e, m_e) in x e)`.
2. **Degree bookkeeping (DB):** per term, per edge `e`:
   `n_e − m_e ≡ (loop multiplicity of e) + ∑_{p∈S} σ_p·(incidence of e
   in p) (mod N_c)` where `σ_p ∈ {±1}` records which trace (or
   conjugate) the term took from `f_p`.  DEFINE the term's chain as
   `indicatorChain S σ : P → ZMod N_c`; the per-edge degree balance
   `N_c ∣ (n_e − m_e)` for ALL `e` is then literally
   `chainBoundary₂ σ = loopChain C` over `ZMod N_c`.
3. **Kill (K):** if some `e₀` is unbalanced, write the integrand as
   `F₀(x e₀)·F₁` (`F₁` ignores `e₀` — funext over the other factors),
   apply `integral_single_coord_marginal`, then
   `sunHaarProb_fundMonomial_integral_zero` at `e₀` ⇒ the term is `0`.
4. **Join (J):** contrapositive — `T_S ≠ 0` ⇒ some index-term has all
   edges balanced ⇒ its `σ`-chain satisfies `∂₂σ = loopChain C` with
   `chainSupport σ ⊆ S` ⇒ `chainArea (loopChain C) ≤ |S|`
   (`chainArea_le_card_of_support_subset`).  This is AL5's statement,
   discharged.

**Lean order:** TE first (self-contained `Matrix` lemma, `L0` or
`ClayCore` level), then `loopChain` (the `1`-chain of a Wilson loop —
needs the loop as an edge list with orientations, cf. `WilsonLine`),
then DB+K per-term, then J.  Estimated 2–3 sessions; TE and
`loopChain` are independent and can be built/verified separately.

**TE-1 CLOSED** (`ClayCore/TracePathExpansion.lean`): `pathSum`
(recursive path-sum, chosen over `Fin L → ι` indexing so downstream
inductions peel one edge structurally), `list_prod_apply`
(`l.prod i j = pathSum l i j`), `trace_list_prod_eq_sum_pathSum`
(trace = sum over closed paths).  Oracle clean — `[propext,
Quot.sound]` only.
**TE-1b CLOSED** (same file): the closed `Fin`-indexed forms —
`pathSum_eq_sum_vertexSeq` (`pathSum l i j = ∑ v : Fin (L+1) → ι,
δ(v 0 = i)·δ(v last = j)·∏_{idx} (l.get idx)(v idx.castSucc)(v
idx.succ)`, by list induction transporting the sum along
`Fin.consEquiv` and collapsing the head vertex through a common
`w`-sum normal form) and `trace_list_prod_eq_sum_closedSeq` (trace =
sum over CLOSED vertex sequences, `δ(v last = v 0)`).  For fixed `v`
the integrand is a positionwise product of single matrix entries —
the exact input of `prod_comp_eq_prod_fiber`.  Oracle clean.
House notes: normalize `(M :: l).length` to `l.length + 1` via `show`
BEFORE `Fintype.sum_equiv` (binder types can't be simp-rewritten);
`simp only [Fin.consEquiv_apply]` (from `@[simps]`) reduces the equiv
application; rewrite ites under `Fin.cons` with `simp only [hv0,…]`
not `rw` (Decidable-instance motive); `congr 1` closes the
`Fin.prod_univ_succ` head factor on its own (cons-defeq).
**TE-2 CLOSED** (`ChainComplex.lean`): `loopChain` (orientation-odd
signed edge count `count e − count (reverse e)`, matching the repo's
`wilsonLine`-over-edge-list convention where backward traversal IS
the reversed edge), `loopChain_reverse` (orientation-odd),
`loopChain_append` (additive under concatenation, mirroring
`wilsonLine_append`).  Oracle clean.
**K (abstract form) CLOSED** (`ClayCore/GaugeMarginal.lean`):
`prod_comp_eq_prod_fiber` (a positionwise product `∏ᵢ Fᵢ(x(π i))`
regroups into per-edge fiber factors `∏ₑ ∏_{i: π i = e} Fᵢ(x e)` —
what decouples one closed-path term of the trace expansion) and
`integral_positionProduct_eq_zero` (the one-unbalanced-edge kill: the
gauge expectation of a positionwise edge-product observable vanishes
as soon as ONE positive edge's collected factor has zero Haar mean).
Both oracle clean.  House note: state grouping lemmas with
`[DecidableEq ε]`, NOT under `open Classical in` — otherwise the
`filter`'s `DecidablePred` instance in the abstract lemma
(`Classical.propDecidable`) mismatches the derived instance at the
concrete type, and `exact` fails with two identically-printed types.
**DB-1 CLOSED** (`ClayCore/SchurEntryNAlitySelection.lean`):
`sunHaarProb_decoratedEntryProduct_integral_zero` — the
`Finset`-indexed selection rule: `∫ ∏_{i∈s} (if dec i then U_{aᵢbᵢ}
else conj U_{aᵢbᵢ}) dHaar = 0` unless `N_c` divides
`#(dec true) − #(dec false)`.  Oracle clean.  Proved by splitting the
product with `prod_filter_mul_prod_filter_not`, reindexing each block
through `Finset.equivFin` (`prod_coe_sort` + `Fintype.prod_equiv`),
and applying the banked `fundMonomial` rule.  This is the exact shape
of one per-edge fiber factor after `prod_comp_eq_prod_fiber`; J never
touches `Fin`-indexed monomials.
**TE map-forms + J-1 CLOSED** (`TracePathExpansion.lean`,
`ClayCore/WilsonLoopMonomial.lean`): `pathSum_map_eq_sum_vertexSeq` /
`trace_prod_map_eq_sum_closedSeq` (the expansion stated over `(es, f)`
directly — binder types stay at `es.length`, NO `List.length_map`
casts; same induction); `sun_inv_val_apply` (unitarity entrywise:
`(U⁻¹)_{ab} = conj U_{ba}`, via `Inv := star` on
`specialUnitaryGroup`); `posEdgeOf` + `posToFun_val_apply` (the
decoration: forward traversal reads an entry of the positive-edge
coordinate, backward reads the conjugated transposed entry);
`wilsonLine_val` (`SubmonoidClass.coe_list_prod` bridge); and the
master **`trace_wilsonLine_eq_sum_decorated`**: the Wilson-loop trace
in positive-edge coordinates = sum over closed vertex sequences of
positionwise DECORATED entries — for fixed `v` exactly the input of
`prod_comp_eq_prod_fiber` + the decorated selection rule.  All six
oracle clean.
**J-2 CLOSED** (`WilsonLoopMonomial.lean`):
`integral_trace_wilsonLine_eq_zero` — **the β=0 `N`-ality selection
rule for Wilson loops**: `∫ tr(W_es) dμ_gauge = 0` whenever one
positive edge has `N_c`-unbalanced signed traversal count.  The first
END-TO-END run of the whole pipeline: decorated expansion →
`integral_finset_sum` (integrability from `entry_norm_bound_of_unitary`
+ `Integrable.bdd_mul`) → per-`v` `integral_const_mul` (term-mode
`.trans`, keyed `rw` fails) → grouping/kill → DB-1.  In particular:
every open line and every fundamental loop traversing some edge
exactly once has zero Haar expectation.  Oracle clean.  House notes:
when an ite-rewrite must hit several differently-branched ites with
the same condition, `simp only [if_pos hs]`/`[if_neg hs]` (one pass,
all instantiations) — full `simp [hs]` normalizes `get`→`getElem` and
orphans `hs`.
**Open:** DB-2 (add plaquette activities to the integrand: term
chains `σ : P → {±1}`, balance ⟺ `∂₂(indicatorChain S σ) = loopChain
C` over `ZMod N_c`), J-3 (contrapositive join → `chainArea_le_card_of_
support_subset`), then AL6.  J-2 is the template: DB-2/J-3 extend its
integrand by `∏_{p∈S} f_p` with the activities expanded by
`integral_mul_prod_one_add` and each term routed through the SAME
grouping/kill.

**Then AL6:** `|⟨W_C⟩·Z| ≤ ∑_{|S| ≥ Area} (N_c·δ^{|S|})·(entropy)` —
the `x/(1−Kx)` tail pattern from the correlator campaign, plus the
non-vacuity window.

## 5. What this plan does not promise

The area law is still M3-lattice-side (Osterwalder–Seiler).  It does
not touch the continuum, OS reconstruction, or the Clay problem
(distance: ~0%, unchanged).  Peter–Weyl remains the long-term route
to the full character-expansion toolbox; this plan only removes it
from the critical path of the area law, as the shortcut removed it
from the critical path of correlator decay.
