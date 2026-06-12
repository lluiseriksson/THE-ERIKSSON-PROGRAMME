# AREA-LAW EXACT-ACTIVITY PLAN (post-campaign refinement 1)

**Date:** 2026-06-12.  **Status: CAMPAIGN COMPLETE** — headline
`finite_volume_area_law_exp` (`YangMills/ClayCore/WilsonLoopMonomial.lean`)
machine-checked, oracle `[propext, Classical.choice, Quot.sound]`:

```
‖∫ tr(W_C)·∏_p exp(z_p)‖
  ≤ N_c · 2^{#P} · (e^{2δN_c}−1)^{Area(C)} · (e^{2δN_c})^{#P}
```

for the TRUE Wilson Boltzmann factor `z_p = c_p·tr H_p + c_p'·conj tr H_p`,
`‖c_p‖,‖c_p'‖ ≤ δ` — NO smallness hypothesis, every `δ ≥ 0`; the area
factor decays as `(2δN_c)^{Area}` at strong coupling, recovering (and
strictly extending) the linearized law.  Upgrades
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
| E3b | **Multiplicity join** — `powerTraceObservable` (the generic exp-series term) + `chainAreaA_le_card_support_of_integral_pow_ne_zero`: nonzero expectation ⇒ `Area ≤ #{p : jₚ+kₚ ≠ 0}`, via repeated lines over `Σ p, Fin jₚ ⊕ Fin kₚ` + the sharp join.  House note: `letI` does NOT parse inside binder types — factor the `Fintype`-needing observable into a standalone `def` and reference it in hypotheses. | **CLOSED** (oracle clean) |
| E4a | **Survivor toolkit** — `measurable_powerTraceObservable`, `norm_powerTraceObservable_le` (pointwise `N_c^{1+Σ(j+k)}` via `Finset.prod_pow_eq_pow_sum`), `norm_integral_powerTraceObservable_le`, `integrable_powerTraceObservable`. | **CLOSED** (oracle clean) |
| E4b-1 | **Stage 1 (pointwise expansion + domination):** `summable_norm_pow_div_factorial`, `prod_exp_eq_tsum_prod_pow` (`∏ exp(zᵢ) = ∑'_m ∏ zᵢ^{mᵢ}/mᵢ!`), `summable_prod_pow_div_factorial` (the E2 dominating family).  House notes: write factorial casts as `Nat.factorial k` (the `(k ! : ℂ)` ascription misparses); provide `summable_norm_pi_prod`'s family EXPLICITLY via `(a := …)` — goal-driven unification against a symbolic `∏` hangs `isDefEq`. | **CLOSED** (oracle clean) |
| E4b-1b | **Tail substrate:** `tsum_pi_prod_nonneg` (real Pi-Cauchy for nonneg families, by `Complex.ofReal_injective` transport of E1), `tsum_pow_div_factorial` (`= exp x`), `tsum_pow_div_factorial_succ` (`= exp x − 1`, via `Summable.tsum_eq_zero_add`).  **T1 also CLOSED:** `tsum_shifted_prod_pow_div_factorial` — the per-`S` constrained sum factorizes EXACTLY: `∑'_{m : ∀p∈S, mₚ≥1} ∏ x^{mₚ}/mₚ! = (e^x−1)^{#S}·(e^x)^{#ι−#S}`, via the shift-injection `φ n = n + 1_S` + `Function.Injective.tsum_eq` (support ⊆ range) + `tsum_pi_prod_nonneg` with the mixed family.  **T2+T3 ALSO CLOSED:** `tsum_constrained_prod_pow_div_factorial_le` — **THE TAIL ESTIMATE**: `∑'_{m : #supp m ≥ A} ∏ x^{mₚ}/mₚ! ≤ 2^{#ι}·(e^x−1)^A·(e^x)^{#ι}`, via the pointwise union bound over `powersetCard A` (`exists_subset_card_eq` + `single_le_sum`), `Summable.tsum_le_tsum`, the swap `Summable.tsum_finsetSum`, T1 per `S`, and `choose ≤ 2^n` (`Nat.sum_range_choose`).  House notes: bare `tsum_le_tsum`/`tsum_finsetSum` don't exist — they're `Summable.`-namespaced (SummationFilter refactor); `simp only` does NOT close trivial `≤`-goals — append `le_rfl`. | **TAIL CLOSED** (oracle clean) |
| E4b-2a | **Per-multiplicity dichotomy** — `norm_integral_exp_term_le`: `‖∫ tr(W_C)·∏ zₚ^{mₚ}/mₚ!‖ ≤ if Area ≤ #supp m then N_c·∏(2δN)^{mₚ}/mₚ! else 0`.  Survivors: `le_trans (norm_integral_le_of_norm_le_const …) ?_` (refine-into-goal so `f` unifies BEFORE the tactic-lambda elaborates — `have hb := …` with a `by`-bound proof leaves `f` a meta and sticks `NormMulClass`); per-factor `gcongr` from `‖zₚ‖ ≤ 2δN_c`.  Kill: per-p binomial `add_pow` + `Finset.sum_div`, `Finset.prod_univ_sum`, per-`t` regroup (`mul_pow` + `ring`), `Finset.prod_mul_distrib`, `powerTraceObservable es t (m−t) A := rfl`, then `integral_finset_sum`/`integral_const_mul` and the E3b join contrapositive with `supp(t + (m−t)) = supp m` (piFinset-range + omega).  House notes: third arg of `mul_le_mul` for a ∏-of-norms is `Finset.prod_nonneg`, not `norm_nonneg`; watch paren balance on multi-line `(X^t * star Y^{m−t})` groups — a doubled `((` surfaces as "unexpected ':='" lines later. | **CLOSED** (oracle clean) |
| E4b-2 | **Final assembly** — `finite_volume_area_law_exp`: pointwise `prod_exp_eq_tsum_prod_pow` + `tsum_mul_left.symm` → E2 swap → `norm_tsum_le_tsum_norm` + `Summable.tsum_le_tsum` against the E4b-2a ite-family (summable by comparison with the dominating weights) → factor `N_c` out (`split_ifs`-congr + `tsum_mul_left`) → `tsum_constrained_prod_pow_div_factorial_le` at `x := 2δN_c`.  **CRITICAL HOUSE NOTE (the whnf-hang and its cure):** applying `integral_tsum_of_bounded` FORWARD (`have hswap := integral_tsum_of_bounded μ (fun m A => …big…) (fun m => …) hFm hFb hcw hcs`) hangs `whnf` unboundedly (>1.6M heartbeats) — the unannotated `F`-lambda's binder type is the implicit `?κ`, its postponed elaboration drives non-pattern unification through the concrete `∏ p : P` family.  The cure is the EXPECTED-TYPE-DRIVEN form: ascribe the full equation and apply with underscores, `have hswap : (∫ A, ∑' m, …) = ∑' m, ∫ A, … := integral_tsum_of_bounded _ _ _ hFm hFb hcw hcs` — compiles in seconds (1M-heartbeat headroom kept for safety).  Same lesson as the E1 `(a := …)` rule: never let a tsum/Summable lemma INFER a family containing a symbolic `∏`; hand it the family (here: via the goal ascription). | **CLOSED** (oracle clean) |

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

The constant is finite-volume (`2^{#P}·e^{2δN_c·#P}`); the
volume-uniform version (connected-support resummation against `Z`)
remains the separate recorded refinement, as does Peter–Weyl proper.
The Wilson-action coefficients `c_p = c_p' = β/(2N_c)` (real β)
instantiate the hypotheses with `δ := β/(2N_c)`, i.e.
`2δN_c = β`: the bound reads
`N_c·2^{#P}·(e^β−1)^{Area}·e^{β·#P}` — genuine area-law decay for
`β < ln 2`.
