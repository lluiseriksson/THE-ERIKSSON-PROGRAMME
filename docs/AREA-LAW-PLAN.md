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
| AL4 | factorized expansion of `⟨W_C⟩·Z` with per-edge integration (the `WeightedGas` engine + AL3).  **Substrate CLOSED:** `L1_GibbsMeasure/EdgeFactorization.lean` — `integral_mul_of_disjoint_deps_complex` (the `ℂ`-valued two-block independence factorization, twin of the ℝ engine) and `integral_single_coord_marginal` (single-coordinate split-off `∫F₀(x e₀)·F₁ = ∫F₀·∫F₁`, the per-edge integration step; iterate over edges).  Oracle clean.  House note: at `ℂ` the bare `rw [integral_prod_mul]` fails on hidden instance arguments even when pattern and target PRINT identically — compose in term mode (`hmul.trans (congrArg₂ (·*·) h1F.symm h1G.symm)`); defeq checking succeeds where keyed matching fails.  Remaining: the binomial expansion `⟨W_C⟩·Z = ∑_S ∫ W_C ∏_{p∈S} f_p` and the per-edge monomial bookkeeping wiring into AL3. | substrate done | 1 session |
| AL5 | the spanning-surface lower bound (AL1+AL2 ⇒ nonzero terms have `|S| ≥ Area`) | new | 1–2 sessions |
| AL6 | entropy + tail ⇒ `|⟨W_C⟩| ≤ C₀·r^{Area}`; non-vacuity window | banked patterns | 1 session |

Total: a 6–10 session campaign — smaller than the roadmap's
Peter–Weyl path (its L1 alone was 2500–5000 LOC, HIGH risk), with the
single high-novelty item being AL1/AL5 (discrete surface theory).

## 4. What this plan does not promise

The area law is still M3-lattice-side (Osterwalder–Seiler).  It does
not touch the continuum, OS reconstruction, or the Clay problem
(distance: ~0%, unchanged).  Peter–Weyl remains the long-term route
to the full character-expansion toolbox; this plan only removes it
from the critical path of the area law, as the shortcut removed it
from the critical path of correlator decay.
