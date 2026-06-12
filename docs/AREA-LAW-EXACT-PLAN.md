# AREA-LAW EXACT-ACTIVITY PLAN (post-campaign refinement 1)

**Date:** 2026-06-12.  **Status:** design.  Upgrades
`finite_volume_area_law` (linearized activities, `docs/AREA-LAW-PLAN.md`,
COMPLETE) to the genuine Wilson Boltzmann factor.

## 1. Why the linear class is not enough — and why the kill survives

The completed area law covers `∏_p (1 + f_p)` with `f_p` a LINEAR
combination of `tr Hₚ`/`conj tr Hₚ`.  The true Wilson factor is
`∏_p exp(zₚ)`, `zₚ := c_p·tr Hₚ + c_p'·conj tr Hₚ` — bounded
measurable, but NOT in the linear class, and the kill genuinely needs
the `N`-ality structure (a general bounded activity has no selection
rule).  The route is the exp-SERIES: every term of
`∏_p ∑_k zₚᵏ/k!` is `const · ∏(traces with MULTIPLICITIES)` — and the
multi-line kill (`integral_prod_trace_wilsonLine_eq_zero_of_sum_loopChain_ne_zero`)
already handles repeated lines: the fiber-sum coefficient chain
`σ' p = (2jₚ − mₚ) mod N_c` was built multiplicity-ready (no
injectivity was used in the join).

## 2. Brick ladder

| Brick | Content | Status |
|---|---|---|
| E1 | **Pi-Cauchy product** — `summable_norm_pi_prod`, `tsum_pi_prod`, `tsum_pi_prod'` (`L1_GibbsMeasure/ExpActivityExpansion.lean`).  House note: unifying `Summable`-lemma metas against families containing a SYMBOLIC `∏ i : Fin n` hangs `whnf` (it unfolds `Finset.univ`) — hide the product behind `set G := fun m => ∏ …` before applying, unfold via the set-equation in the congr step. | **CLOSED** (oracle clean) |
| E2 | **∫↔∑' interchange** — `integral_tsum_of_bounded`: measurable + pointwise-dominated-by-summable ⇒ swap, via `integral_tsum` (enorm form, `ofReal_norm_eq_enorm` + `ENNReal.ofReal_tsum_of_nonneg`). | **CLOSED** (oracle clean) |
| E3a | **Sharp join** — `chainAreaA_loopChain_le_card_image_of_integral_ne_zero`: the join's conclusion sharpened from `≤ m` (line count) to `≤ (image ps).card` (DISTINCT plaquette count) — the proof already had it; the old `≤ m` form re-derived as a corollary.  Repeated `ps`-values = multiplicities, so the multiplicity bound `Area ≤ #supp m` is now a direct instantiation. | **CLOSED** (oracle clean) |
| E3b | **Per-m σ-split:** `zₚ^{mₚ}` via `add_pow` (binomial) → per-`(m, j ≤ m)` term = const · multi-line family over `Σ p, (Fin (j p) ⊕ Fin (k p))` enumerated by `equivFin`; powers→repeated factors via `Finset.prod_const` + `Fintype.prod_sum_type` + `Fintype.prod_sigma'`; then E3a with `image ps = supp m` (sigma-fiber nonempty ↔ `mₚ ≠ 0`). | open |
| E4 | **Tail:** `∑_{m : Area ≤ #supp} ∏ (2δN_c)^{mₚ}/mₚ! ≤ (e^{2δN_c}−1)^{Area}·e^{2δN_c·#P}`-type bound ⇒ `‖∫ tr(W_C)·∏ exp(zₚ)‖ ≤ N_c·e^{2δN_c·#P}·(e^{2δN_c}−1)^{Area}`. | open |

Finite-volume constant again (`e^{c·#P}`); volume-uniformity is the
OTHER refinement (connected-support resummation against `Z`,
separate campaign — see `AREA-LAW-PLAN.md` refinements note).

## 3. Estimated effort

E1: 1 session (tsum plumbing).  E2: 1 session.  E3: 1–2 sessions
(binomial + sigma-with-multiplicity bookkeeping; the join template is
`chainAreaA_loopChain_le_of_integral_ne_zero`).  E4: 1 session.
Total 4–6.  No new mathematics — the campaign's novelty was spent in
AL5; this is analysis plumbing on a verified skeleton.

## 4. What this does not promise

Still M3-lattice-side, finite-volume.  No continuum, no OS
reconstruction.  Distance to Clay: ~0% (<0.1%), unchanged.
