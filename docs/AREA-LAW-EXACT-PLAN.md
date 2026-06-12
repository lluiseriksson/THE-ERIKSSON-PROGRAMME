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
| E1 | **Pi-Cauchy product:** `∏_{i : ι} ∑'_k a i k = ∑'_{m : ι → ℕ} ∏_i a i (m i)` for norm-summable `ℂ`-families over a Fintype.  Mathlib has only the two-factor `tsum_mul_tsum`; induct over `Fin n` via `ℕ × (Fin n → ℕ) ≃ (Fin (n+1) → ℕ)` (`Fin.consEquiv` + `Equiv.tsum_eq`), transport to `ι` by `Fintype.equivFin`. | open |
| E2 | **∫↔∑' interchange:** `∫ ∑'_m F_m = ∑'_m ∫ F_m` via `MeasureTheory.integral_tsum` (norm-summable dominating family: `∑_m ∏ δ^{mₚ} N^{mₚ}/mₚ! = e^{δN·#P} < ∞`). | open |
| E3 | **Per-m σ-split:** `zₚ^{mₚ}` via `add_pow` (binomial) → per-`(m, j ≤ m)` term = const · multi-line family with plaquette `p` repeated `mₚ` times (index `Σ p, Fin (m p)`); kill iff the chain `σ' p = (2jₚ − mₚ)` satisfies `∂₂A σ' = −loopChain C`; surviving support `{p : mₚ ≠ 0}` ⊇ a spanning set ⇒ `Area ≤ #supp m`. | open |
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
