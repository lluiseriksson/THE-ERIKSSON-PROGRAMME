/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.ConcreteGaugeRGTerminalGate

/-!
# The physical-exponent terminal gate and the k-step support metric
# (C6 phase B-1^6)

`docs/C6-BRIDGE-CHARTER.md`, AMENDMENT 6 (2026-07-13).  The 5.98 verdict on
B-1^5 accepted the kTerm non-circularity and named the next blocker: THE
DECAY VARIABLE — the terminal consumer concludes decay in the RENORMALIZED
coordinate `u` (a fine-lattice gap `gap/2^n → 0`), not in the physical
separation `2^n·u`.  This module addresses the two Amendment-6 items.

## Item 1 — the physical-exponent terminal gate

* **`PhysicalTerminalScaleWilsonGate`** — EXACTLY the B-1^5
  `TerminalScaleWilsonGate` (constants exists-first before every base `M₀`
  and depth `n`; depths `1 ≤ n` only; IR clause SYNTACTICALLY at
  `fun _ => kTerm n`; UV clauses only at `k < kTerm n`; windowed
  nonvanishing data clause) with ONE change: the IR/UV exponents demand
  decay in the PHYSICAL variable `((2^n·u : ℕ) : ℝ)` (the B-1'''' fidelity
  exponent shape) instead of the renormalized `(u : ℝ)`.  Everything about
  `kTerm` — the fixed definition, `terminalGate_IR_index_eq = rfl`,
  `rsc_is_difference = rfl`, `scaledCovEff_zero_physical = rfl` — is
  consumed unchanged from the B-1^5 module.
* **`wilson_physical_mass_gap_of_physicalTerminalGate`** — the consumer:
  one pack `(C, gap = min ε c0)` quantified BEFORE every base and depth,
  concluding `|C(2^n·u)| ≤ C·exp(−gap·(2^n·u))` — decay in the PHYSICAL
  distance with the gap INDEPENDENT of `n` and `M₀` (visible in the
  quantifier order of the conclusion's type).  Same five-step chain as the
  B-1^5 consumer; only the evaluation point of the exponential changed.
* **`terminalScaleGate_of_physicalTerminalGate`** — COMPARISON, proved:
  the physical gate implies the renormalized B-1^5 gate (the physical
  clauses are pointwise stronger because `u ≤ 2^n·u`, i.e. `1 ≤ 2^n`,
  proved in `renormalized_le_physical_sep`).  The new gate is therefore a
  strengthening, stated as a theorem; the CONVERSE is NOT claimed and NOT
  consumed anywhere.

## Item 2 — the k-step support metric (the corrected recursion, proved)

* **`iterEmbed`** — the `k`-fold coarse-site embedding up the tower
  (`iterEmbed_coord`: every coordinate is EXACTLY `2^k` times the anchor
  coordinate — no wrap, the doubled value stays inside the doubled torus).
* **`kStepBlockSupport_source_in_ball`** — THE MASTER RADIUS THEOREM, by
  induction on `k`: every edge of the `k`-step transported support of a
  plaquette `P` has its source at
  `shiftIter (shiftIter (iterEmbed … P.site k) P.dir1 a) P.dir2 b` with
  the SHARPENED invariant `a + [dir = dir1] ≤ 2^k` and
  `b + [dir = dir2] ≤ 2^k`, and its direction in `{P.dir1, P.dir2}` (the
  support never leaves the plaquette's plane).  The direction-correlated
  `+1` bookkeeping is exactly what makes the induction close: a fine-B
  edge shifts one extra step ONLY along its own direction, so the step is
  `a' + ε ≤ 2·(a + ε) ≤ 2^{k+1}` — strictly within the Amendment-6 budget
  `r_{k+1} ≤ 2·r_k + 2`.  Consequences:
  - **`kStepBlockSupport_radius`** — the Amendment-6 form: for `1 ≤ k` the
    offsets satisfy `a, b ≤ 2^{k+1} − 2` (via `kStep_radius_le_amendment`:
    `2^k ≤ 2^{k+1} − 2` for `k ≥ 1`).  The PROVED sharp radius is `2^k`;
    at `k = 0` the honest radius is the plaquette's own unit extent
    (offsets `≤ 1`), consistent with the amendment's `r_0 = 0`
    anchor-convention plus the separate carrier slack.
  - **`kStepBlockSupport_one`** — consistency, by `rfl`: one step of the
    tower support IS `blockPlaquetteSupport` (the B-1'''' object).
* **`kStepSupport_canonical_separation_walk` / `_dist`** — THE k-STEP
  SEPARATION THEOREM for the canonical pair at coarse separation `τ`
  (window `1 ≤ τ`, `2τ ≤ M`, coarse size `M = towerSize M₀ r` — the
  window CONTAINS the Amendment-6 window `4τ ≤ M` and is exactly what the
  terminal tie needs): any fine plaquettes whose supports meet the two
  `k`-step transported supports on the size-`2^k·M` torus satisfy
  `2^k·τ − (2^k + 1) ≤ length` for EVERY touch-walk between them (hence
  for `dist` when reachable).  The slack `2^k + 1` = sharp support radius
  `2^k` + one carrier-internal offset — derived from the ZMod
  circular-potential argument exactly as in the one-step `c = 3` proof
  (wrap-safe: the window keeps the residue strictly inside `(0, 2^k·M)`).
  At `k = 1` this reproduces the B-1'''' constant EXACTLY: `2τ − 3`
  (`kStepSeparation_one`).  This bound is STRONGER than the Amendment-6
  target `2^k·τ − 2·(2^{k+1} − 2) − c` (whose slack is larger); no weaker
  statement is registered.
* **THE TERMINAL-STAGE TIE (the instance the gate consumes, NOT a
  floating generic statement):** `terminalIR_is_canonical_pair_correlator`
  (by `rfl`) exhibits the gate's IR object — `scaledCanonicalCovIR` at the
  syntactic index `fun _ => kTerm n` — as the truncated correlator of the
  `kTerm n`-fold blocked measure AT the canonical pair
  `(P₀, P_{2u})` on the base torus (`terminal_stage_size`,
  `terminal_stage_sep_index`).  The separation theorems are then
  INSTANTIATED at exactly that pair and exactly `k = kTerm n`
  (`terminalSupport_canonical_separation_walk` / `_dist`), under the
  GATE'S OWN WINDOW `1 ≤ u ∧ 4u ≤ M₀` — a condition on `(u, M₀)` only,
  with NO `n` in the hypotheses (`terminal_window_nonempty`).  Concrete
  strict positivity at `k = kTerm n = n` for all `n ≥ 1, u ≥ 1`
  (`terminalSupport_separation_pos`) and strict growth in the depth
  (`terminalSupport_separation_strict_growth`).
* **`kStepSeparation_pos` / `kStepSeparation_strictMono`** — THE PROVED
  POSITIVITY WINDOW, stated exactly: for `τ ≥ 2` and `k ≥ 1` the lower
  bound `2^k·τ − (2^k + 1)` is strictly positive and strictly increasing
  in `k`.  At `τ = 1` the bound ℕ-truncates to `0` (vacuous-but-true, same
  as the one-step theorem at `τ = 1`); at `k = 0` it is `τ − 2`, positive
  only from `τ ≥ 3` — both stated openly, neither claimed positive.

## Self-attack inventory (mandatory, outcomes stated honestly)

(a) THE `n = 0` ROUTE against the physical gate: unstatable — the gate
    quantifies ONLY depths `1 ≤ n`, its IR clause is syntactically at
    `fun _ => kTerm n` with `1 ≤ kTerm n` (`kTerm_pos`), and `k = 0`
    enters only inside the first difference (`rsc_is_difference`, by
    `rfl`, inherited).  The physical strengthening changes ONLY exponents,
    so every B-1^5 exclusion (fixed `kTerm`, no clamp, no standalone
    unblocked bound) is inherited verbatim.
(b) COMPARISON DIRECTION: physical ⟹ renormalized is the PROVED theorem
    (`exp(−c·2^n·u) ≤ exp(−c·u)` since `u ≤ 2^n·u`); the converse would
    need `exp(−c·u) ≤ exp(−c·2^n·u)`, which is FALSE for `n ≥ 1`, `u ≥ 1`,
    `c > 0` — the converse is not stated, not claimed, not consumed.
(c) GAP INDEPENDENCE: `(C, gap)` are bound BEFORE `M₀` and `n` in the
    consumer's conclusion; a depth-dependent gap is unstatable against
    that type.
(d) WRAP-AROUND at the window edge `4τ = M`: the separation proof needs
    `τ + 2 ≤ M` (mod removal) and `2·(2^k·τ) ≤ 2^k·M` (residue window) —
    both hold AT the edge `4τ = M` with `τ ≥ 1`; checked in the proof, no
    strictness is lost.
(e) SMALL `M` / `τ = 1` EDGES: the window `1 ≤ τ ∧ 4τ ≤ M` forces
    `M ≥ 4`; at `τ = 1` the k-step bound truncates to `2^k − 2^k − 1 = 0`
    in ℕ — true and uninformative, exactly like the one-step `2·1 − 3`.
    The positivity theorems demand `τ ≥ 2, k ≥ 1` and prove strictness
    there; no positivity is claimed outside that window.
(f) RADIUS AT `k = 0`: the amendment's closed form `2^{k+1} − 2` FAILS at
    `k = 0` (it gives 0, but the plaquette's own support has offsets 1);
    `kStepBlockSupport_radius` therefore carries the honest hypothesis
    `1 ≤ k`, and the master theorem carries the sharp `2^k` bound at every
    `k` including `k = 0` (where `2^0 = 1` is exactly the unit extent).

## Residual-risk inventory (open, stated before any external verdict — NO
## "delivered" claims are made anywhere)

(i) NO WITNESS of `PhysicalTerminalScaleWilsonGate` is provided or
    claimed; its satisfiability for the Wilson data is the open
    mathematics, strictly harder than the B-1^5 gate it implies.
(ii) De-lacunarization from positive scales remains OPEN: odd physical
    separations are unreachable at `n ≥ 1`
    (`odd_separation_needs_base_scale`), and nothing in this module
    interpolates them.
(iii) The k-step separation is a statement about fine plaquettes MEETING
    the transported supports (touch-walk/`dist` lower bound); no
    edge-set-valued metric space is introduced, no upper support-distance
    bound is proved, and the lower bound is not claimed sharp.  The
    k-FOLD PULLBACK LOCALITY — that the terminal observable's fine-level
    dependence is CONTAINED in the k-step support, i.e. the k-fold
    composition of the one-step `blockMap_holonomy_congr` through the
    tower's measure pushforwards — is NOT formalized here; the terminal
    tie is geometric (the consumed pair, index, and window are exactly
    the gate's, by `rfl` and instantiation), not an operational
    support-of-observable theorem.  Named as the next missing lemma.
(iv) The support metric is geometric bookkeeping; no new analytic
    estimate is proved anywhere in this module.  The canonical correlator
    remains a finite-torus object; "mass-gap-shaped" is the only
    permitted phrasing.  Clay distance ~0% (<0.1%), unchanged.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

open YangMills MeasureTheory GaugeConfig

/-! ### 1.  Item 1: the physical-exponent terminal gate -/

section PhysicalGate

/-- The renormalized separation index is dominated by the physical one:
`u ≤ 2^n·u`, because `1 ≤ 2^n`. -/
theorem renormalized_le_physical_sep (n u : ℕ) : u ≤ 2 ^ n * u :=
  Nat.le_mul_of_pos_left u (pow_pos (by norm_num) n)

/-- The physical-exponent bound is pointwise STRONGER than the
renormalized one: `exp(−c·2^n·u) ≤ exp(−c·u)` for `c ≥ 0`. -/
theorem physical_exp_le_renormalized_exp {c : ℝ} (hc : 0 ≤ c) (n u : ℕ) :
    Real.exp (-(c * ((2 ^ n * u : ℕ) : ℝ))) ≤ Real.exp (-(c * (u : ℝ))) := by
  apply Real.exp_le_exp.mpr
  have h1 : (u : ℝ) ≤ ((2 ^ n * u : ℕ) : ℝ) := by
    exact_mod_cast renormalized_le_physical_sep n u
  have h2 : c * (u : ℝ) ≤ c * ((2 ^ n * u : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left h1 hc
  linarith

variable {d : ℕ} [NeZero d]

/-- **THE PHYSICAL-EXPONENT TERMINAL GATE (B-1^6 item 1).**  Structurally
IDENTICAL to `TerminalScaleWilsonGate` — constants exists-first; bases
`4 ≤ M₀` and depths `1 ≤ n` only; probability clause; IR clause
SYNTACTICALLY at `fun _ => kTerm n` (the terminal correlator of the
maximally blocked measure, `terminalGate_IR_index_eq = rfl`); UV clauses
only at `k < kTerm n`; windowed nonvanishing data clause — EXCEPT that the
IR/UV exponentials are evaluated at the PHYSICAL separation
`((2^n·u : ℕ) : ℝ)` instead of the renormalized `(u : ℝ)`.  Strictly
stronger than the B-1^5 gate (`terminalScaleGate_of_physicalTerminalGate`).
NO witness is provided or claimed. -/
def PhysicalTerminalScaleWilsonGate (hd : 2 ≤ d) (N_c : ℕ) [NeZero N_c]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (β : ℝ) : Prop :=
  ∃ (g : ℕ → ℝ) (C1 C2 ε c0 βc κ₀ : ℝ),
    0 ≤ C1 ∧ 0 < ε ∧ 0 < c0 ∧ 0 ≤ C2 ∧ 1 < κ₀ ∧ 0 < βc ∧
    (∀ k, 0 < g k) ∧ (∀ k, βc * g k < 1) ∧
    (∀ k, g (k + 1) = g k * (1 - βc * g k)) ∧
    (∀ (M₀ : ℕ) (_ : NeZero M₀), 4 ≤ M₀ → ∀ n : ℕ, 1 ≤ n →
      (∀ k : ℕ, IsProbabilityMeasure (towerMeasure M₀ n
        (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) k)) ∧
      (∀ u : ℕ, 1 ≤ u → 4 * u ≤ M₀ →
        |scaledCanonicalCovIR hd M₀ n
            (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f
            (fun _ => kTerm n) u|
          ≤ C1 * Real.exp (-(ε * ((2 ^ n * u : ℕ) : ℝ)))) ∧
      (∀ u k : ℕ, 1 ≤ u → 4 * u ≤ M₀ → k < kTerm n →
        |scaledCanonicalRsc hd M₀ n
            (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f u k|
          ≤ C2 * Real.exp (-(c0 * ((2 ^ n * u : ℕ) : ℝ))) * g k ^ κ₀) ∧
      (∃ u k : ℕ, 1 ≤ u ∧ 4 * u ≤ M₀ ∧ k < kTerm n ∧
        scaledCanonicalRsc hd M₀ n
          (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f u k ≠ 0))

/-- **COMPARISON (proved): the physical gate implies the renormalized
B-1^5 gate.**  Every physical clause dominates the corresponding
renormalized clause because `u ≤ 2^n·u` (`renormalized_le_physical_sep`),
so `exp(−c·2^n·u) ≤ exp(−c·u)`.  The CONVERSE is not claimed. -/
theorem terminalScaleGate_of_physicalTerminalGate (hd : 2 ≤ d) (N_c : ℕ)
    [NeZero N_c] (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (β : ℝ) (h : PhysicalTerminalScaleWilsonGate hd N_c f β) :
    TerminalScaleWilsonGate hd N_c f β := by
  obtain ⟨g, C1, C2, ε, c0, βc, κ₀, hC1, hε, hc0, hC2, hκ, hβc,
    hpos, hsmall, hrec, hmain⟩ := h
  refine ⟨g, C1, C2, ε, c0, βc, κ₀, hC1, hε, hc0, hC2, hκ, hβc,
    hpos, hsmall, hrec, ?_⟩
  intro M₀ instM hM n hn
  haveI : NeZero M₀ := instM
  obtain ⟨hprob, hIR, hUV, hnz⟩ := hmain M₀ instM hM n hn
  refine ⟨hprob, fun u hu h4u => ?_, fun u k hu h4u hk => ?_, hnz⟩
  · exact le_trans (hIR u hu h4u)
      (mul_le_mul_of_nonneg_left
        (physical_exp_le_renormalized_exp hε.le n u) hC1)
  · refine le_trans (hUV u k hu h4u hk) ?_
    have h1 : C2 * Real.exp (-(c0 * ((2 ^ n * u : ℕ) : ℝ)))
        ≤ C2 * Real.exp (-(c0 * (u : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (physical_exp_le_renormalized_exp hc0.le n u) hC2
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hpos k).le _)

/-- **THE PHYSICAL CONSUMER (item 1's demanded conclusion).**  A witness of
the physical terminal gate yields ONE pack `(C, gap = min ε c0)` —
quantified BEFORE every base `M₀` and depth `n`, so the gap is INDEPENDENT
of both — with `|C(2^n·u)| ≤ C·exp(−gap·(2^n·u))`: decay in the PHYSICAL
distance.  The chain is the B-1^5 one (telescoping ends definitionally at
`kTerm n`; the physical anchor is `scaledCovEff_zero_physical`, by `rfl`;
no `k = 0` clause is consumed); only the exponential's evaluation point
moved from `u` to `2^n·u`. -/
theorem wilson_physical_mass_gap_of_physicalTerminalGate (hd : 2 ≤ d)
    (N_c : ℕ) [NeZero N_c]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (β : ℝ)
    (hgate : PhysicalTerminalScaleWilsonGate hd N_c f β) :
    ∃ C gap : ℝ, 0 < gap ∧
      ∀ (M₀ : ℕ) (_ : NeZero M₀), 4 ≤ M₀ → ∀ n : ℕ, 1 ≤ n →
      ∀ u : ℕ, 1 ≤ u → 4 * u ≤ M₀ →
        |canonicalCorrelator hd
            (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f
            (2 ^ n * u)|
          ≤ C * Real.exp (-(gap * ((2 ^ n * u : ℕ) : ℝ))) := by
  obtain ⟨g, C1, C2, ε, c0, βc, κ₀, hC1, hε, hc0, hC2, hκ, hβc,
    hpos, hsmall, hrec, hmain⟩ := hgate
  have hsum : Summable (fun k => g k ^ κ₀) :=
    marginal_coupling_pow_summable_of_recursion g hβc hpos hsmall hrec hκ
  have hw : ∀ k, 0 ≤ g k ^ κ₀ := fun k => Real.rpow_nonneg (hpos k).le _
  set S : ℝ := ∑' k, g k ^ κ₀ with hS
  have hS0 : 0 ≤ S := tsum_nonneg hw
  refine ⟨C1 + C2 * S, min ε c0, lt_min hε hc0, ?_⟩
  intro M₀ instM hM n hn u hu h4u
  haveI : NeZero M₀ := instM
  obtain ⟨-, hIR, hUV, -⟩ := hmain M₀ instM hM n hn
  set μ := wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β with hμ
  have hdec := scaledCanonical_decomposition hd M₀ n μ f (fun _ => kTerm n) u
  have hphys := scaledCovEff_zero_physical hd M₀ n μ f u
  have hsumbound :
      |covUV_concrete (scaledCanonicalRsc hd M₀ n μ f) (fun _ => kTerm n) u|
        ≤ (C2 * Real.exp (-(c0 * ((2 ^ n * u : ℕ) : ℝ)))) * S := by
    have hamp : (0 : ℝ) ≤ C2 * Real.exp (-(c0 * ((2 ^ n * u : ℕ) : ℝ))) :=
      mul_nonneg hC2 (Real.exp_pos _).le
    have hRk : ∀ k, k ∈ Finset.range (kTerm n) →
        |scaledCanonicalRsc hd M₀ n μ f u k|
          ≤ (C2 * Real.exp (-(c0 * ((2 ^ n * u : ℕ) : ℝ)))) * g k ^ κ₀ := by
      intro k hk
      exact hUV u k hu h4u (Finset.mem_range.mp hk)
    calc |covUV_concrete (scaledCanonicalRsc hd M₀ n μ f) (fun _ => kTerm n) u|
        = |∑ k ∈ Finset.range (kTerm n), scaledCanonicalRsc hd M₀ n μ f u k| := rfl
      _ ≤ ∑ k ∈ Finset.range (kTerm n), |scaledCanonicalRsc hd M₀ n μ f u k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (kTerm n),
            (C2 * Real.exp (-(c0 * ((2 ^ n * u : ℕ) : ℝ)))) * g k ^ κ₀ :=
          Finset.sum_le_sum hRk
      _ = (C2 * Real.exp (-(c0 * ((2 ^ n * u : ℕ) : ℝ)))) *
            ∑ k ∈ Finset.range (kTerm n), g k ^ κ₀ := by
          rw [Finset.mul_sum]
      _ ≤ (C2 * Real.exp (-(c0 * ((2 ^ n * u : ℕ) : ℝ)))) * S :=
          mul_le_mul_of_nonneg_left
            (hsum.sum_le_tsum (Finset.range (kTerm n)) (fun k _ => hw k)) hamp
  have hIRu := hIR u hu h4u
  have hfinal := decay_assembly hC1 hC2 hS0
    (Nat.cast_nonneg (2 ^ n * u)) hIRu hsumbound
  calc |canonicalCorrelator hd μ f (2 ^ n * u)|
      = |scaledCanonicalCovEff hd M₀ n μ f 0 u| := by rw [hphys]
    _ = |scaledCanonicalCovIR hd M₀ n μ f (fun _ => kTerm n) u
          + covUV_concrete (scaledCanonicalRsc hd M₀ n μ f)
              (fun _ => kTerm n) u| := by rw [← hdec]
    _ ≤ (C1 + C2 * S) * Real.exp (-(min ε c0 * ((2 ^ n * u : ℕ) : ℝ))) :=
        hfinal

end PhysicalGate

/-! ### 2.  Item 2: shift/embedding calculus for the k-step support -/

section ShiftCalculus

variable {d : ℕ} [NeZero d]

/-- A single shift commutes past an iterated shift in a DIFFERENT
direction. -/
theorem shift_shiftIter_comm {N : ℕ} [NeZero N] (x : FinBox d N)
    {i j : Fin d} (h : i ≠ j) (b : ℕ) :
    (shiftIter x j b).shift i = shiftIter (x.shift i) j b := by
  induction b with
  | zero => rfl
  | succ b ihb =>
      show ((shiftIter x j b).shift j).shift i
        = (shiftIter (x.shift i) j b).shift j
      rw [FinBox.shift_comm _ j i (Ne.symm h), ihb]

/-- Appending one extra `i`-shift after the plane box, `i ≠ j` (the
inductive-step normal form of the k-step radius proof; applied by `exact`
in the master induction, where the two defeq spellings of the fine torus
size make a `rw` unusable). -/
theorem shiftIter_shift_left {N : ℕ} [NeZero N] (x : FinBox d N)
    {i j : Fin d} (h : i ≠ j) (a b : ℕ) :
    (shiftIter (shiftIter x i a) j b).shift i
      = shiftIter (shiftIter x i (a + 1)) j b := by
  rw [shift_shiftIter_comm _ h b]
  rfl

/-- The coarse-site embedding turns `m` coarse steps into `2m` fine steps
(iterated form of `coarseSiteEmbed_shift`). -/
theorem coarseSiteEmbed_shiftIter {M : ℕ} [NeZero M] (y : FinBox d M)
    (i : Fin d) (m : ℕ) :
    coarseSiteEmbed (d := d) (shiftIter y i m)
      = shiftIter (coarseSiteEmbed y) i (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      show coarseSiteEmbed ((shiftIter y i m).shift i) = _
      rw [coarseSiteEmbed_shift, ih]
      rfl

/-- **The `k`-fold anchor embedding up the tower:** `k` iterations of the
even-sublattice embedding `y ↦ 2y`, typed cast-free through the
definitional `towerSize` doubling. -/
def iterEmbed (M₀ : ℕ) [NeZero M₀] (r : ℕ) (x : FinBox d (towerSize M₀ r)) :
    (k : ℕ) → FinBox d (towerSize M₀ (r + k))
  | 0 => x
  | k + 1 => coarseSiteEmbed (iterEmbed M₀ r x k)

@[simp] theorem iterEmbed_zero (M₀ : ℕ) [NeZero M₀] (r : ℕ)
    (x : FinBox d (towerSize M₀ r)) : iterEmbed M₀ r x 0 = x := rfl

theorem iterEmbed_succ (M₀ : ℕ) [NeZero M₀] (r : ℕ)
    (x : FinBox d (towerSize M₀ r)) (k : ℕ) :
    iterEmbed M₀ r x (k + 1) = coarseSiteEmbed (iterEmbed M₀ r x k) := rfl

/-- **The scaled anchor is exact:** every coordinate of the `k`-fold
embedded site is EXACTLY `2^k` times the anchor coordinate (no wrap: the
doubled value always stays inside the doubled torus). -/
theorem iterEmbed_coord (M₀ : ℕ) [NeZero M₀] (r : ℕ)
    (x : FinBox d (towerSize M₀ r)) (k : ℕ) (j : Fin d) :
    ((iterEmbed M₀ r x k) j).val = 2 ^ k * (x j).val := by
  induction k with
  | zero =>
      show (x j).val = 2 ^ 0 * (x j).val
      rw [pow_zero, one_mul]
  | succ k ih =>
      show 2 * ((iterEmbed M₀ r x k) j).val = 2 ^ (k + 1) * (x j).val
      rw [ih, pow_succ]
      ring

/-- The four support edges of a plaquette, with source AND direction data
(the `rfl`-reduction of `mem_plaquetteSupport_iff`, packaged once). -/
theorem plaquetteSupport_cases {N : ℕ} [NeZero N]
    {p : ConcretePlaquette d N} {e : PosEdge d N}
    (he : e ∈ plaquetteSupport p) :
    (e.1.source = p.site ∧ e.1.dir = p.dir1) ∨
    (e.1.source = p.site.shift p.dir1 ∧ e.1.dir = p.dir2) ∨
    (e.1.source = p.site.shift p.dir2 ∧ e.1.dir = p.dir1) ∨
    (e.1.source = p.site ∧ e.1.dir = p.dir2) := by
  rw [mem_plaquetteSupport_iff] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- One step of fine-support transport, in equation form: the fine edge
keeps the coarse edge's direction, and its source is the doubled coarse
source, possibly shifted ONE extra step along that same direction. -/
theorem fineSupport_source_step {M : ℕ} [NeZero M]
    {S : Finset (PosEdge d M)} {e' : PosEdge d (2 * M)}
    (he' : e' ∈ fineSupport S) :
    ∃ e ∈ S, e'.1.dir = e.1.dir ∧
      (e'.1.source = coarseSiteEmbed e.1.source ∨
       e'.1.source = (coarseSiteEmbed e.1.source).shift e.1.dir) := by
  obtain ⟨e, he, hef⟩ := mem_fineSupport.mp he'
  rw [mem_fineEdgePair] at hef
  rcases hef with rfl | rfl
  · exact ⟨e, he, rfl, Or.inl rfl⟩
  · exact ⟨e, he, rfl, Or.inr rfl⟩

end ShiftCalculus

/-! ### 3.  Item 2: the k-step radius theorem (master induction) -/

section KStepRadius

variable {d : ℕ} [NeZero d]

/-- **THE MASTER k-STEP RADIUS THEOREM (corrected recursion, proved by
induction).**  Every edge of the `k`-step transported support of a
plaquette `P` (i) keeps its direction inside the plaquette plane
`{P.dir1, P.dir2}`, and (ii) has its source inside the plane box at the
`2^k`-scaled anchor with the SHARPENED direction-correlated bounds
`a + [dir = dir1] ≤ 2^k` and `b + [dir = dir2] ≤ 2^k`.  The inductive
step is `offset ↦ 2·offset (+1 only along the edge's own direction)`,
which is strictly within the Amendment-6 budget `r_{k+1} ≤ 2·r_k + 2`;
the closed form is the sharp radius `2^k` (compare
`kStepBlockSupport_radius` for the amendment's `2^{k+1} − 2` form). -/
theorem kStepBlockSupport_source_in_ball (M₀ : ℕ) [NeZero M₀] (r : ℕ)
    (P : ConcretePlaquette d (towerSize M₀ r)) :
    ∀ (k : ℕ), ∀ e ∈ kStepBlockSupport M₀ r (plaquetteSupport P) k,
      (e.1.dir = P.dir1 ∨ e.1.dir = P.dir2) ∧
      ∃ a b : ℕ,
        a + (if e.1.dir = P.dir1 then 1 else 0) ≤ 2 ^ k ∧
        b + (if e.1.dir = P.dir2 then 1 else 0) ≤ 2 ^ k ∧
        e.1.source
          = shiftIter (shiftIter (iterEmbed M₀ r P.site k) P.dir1 a)
              P.dir2 b := by
  have hne : P.dir1 ≠ P.dir2 := Fin.ne_of_lt P.hlt
  intro k
  induction k with
  | zero =>
      intro e he
      rw [kStepBlockSupport_zero] at he
      rcases plaquetteSupport_cases he with ⟨hs, hdr⟩ | ⟨hs, hdr⟩ |
        ⟨hs, hdr⟩ | ⟨hs, hdr⟩ <;> rw [hdr]
      · refine ⟨Or.inl rfl, 0, 0, ?_, ?_, ?_⟩
        · rw [if_pos rfl]; norm_num
        · rw [if_neg hne]; norm_num
        · rw [hs]; rfl
      · refine ⟨Or.inr rfl, 1, 0, ?_, ?_, ?_⟩
        · rw [if_neg (Ne.symm hne)]; norm_num
        · rw [if_pos rfl]; norm_num
        · rw [hs]; rfl
      · refine ⟨Or.inl rfl, 0, 1, ?_, ?_, ?_⟩
        · rw [if_pos rfl]; norm_num
        · rw [if_neg hne]; norm_num
        · rw [hs]; rfl
      · refine ⟨Or.inr rfl, 0, 0, ?_, ?_, ?_⟩
        · rw [if_neg (Ne.symm hne)]; norm_num
        · rw [if_pos rfl]; norm_num
        · rw [hs]; rfl
  | succ k ih =>
      intro e' he'
      have he'' : e' ∈ fineSupport
          (kStepBlockSupport M₀ r (plaquetteSupport P) k) := he'
      obtain ⟨e, he, hdir', hor⟩ := fineSupport_source_step he''
      obtain ⟨hdir, a, b, ha, hb, hsrc⟩ := ih e he
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by
        rw [pow_succ]; ring
      have hEmbed : coarseSiteEmbed e.1.source
          = shiftIter (shiftIter (iterEmbed M₀ r P.site (k + 1)) P.dir1
              (2 * a)) P.dir2 (2 * b) := by
        rw [hsrc, coarseSiteEmbed_shiftIter, coarseSiteEmbed_shiftIter]
        rfl
      rcases hor with hA | hB
      · refine ⟨?_, 2 * a, 2 * b, ?_, ?_, ?_⟩
        · rw [hdir']; exact hdir
        · rw [hdir']
          by_cases hc : e.1.dir = P.dir1
          · rw [if_pos hc]; rw [if_pos hc] at ha; omega
          · rw [if_neg hc]; rw [if_neg hc] at ha; omega
        · rw [hdir']
          by_cases hc : e.1.dir = P.dir2
          · rw [if_pos hc]; rw [if_pos hc] at hb; omega
          · rw [if_neg hc]; rw [if_neg hc] at hb; omega
        · rw [hA]; exact hEmbed
      · rcases hdir with hdi | hdj
        · -- the extra fine step is along `dir1`
          refine ⟨?_, 2 * a + 1, 2 * b, ?_, ?_, ?_⟩
          · rw [hdir', hdi]; exact Or.inl rfl
          · rw [hdir', hdi, if_pos rfl]
            rw [if_pos hdi] at ha
            omega
          · rw [hdir', hdi, if_neg hne]
            rw [hdi, if_neg hne] at hb
            omega
          · rw [hB, hdi, hEmbed]
            exact shiftIter_shift_left (iterEmbed M₀ r P.site (k + 1)) hne
              (2 * a) (2 * b)
        · -- the extra fine step is along `dir2`
          refine ⟨?_, 2 * a, 2 * b + 1, ?_, ?_, ?_⟩
          · rw [hdir', hdj]; exact Or.inr rfl
          · rw [hdir', hdj, if_neg (Ne.symm hne)]
            rw [hdj, if_neg (Ne.symm hne)] at ha
            omega
          · rw [hdir', hdj, if_pos rfl]
            rw [hdj, if_pos rfl] at hb
            omega
          · rw [hB, hdj, hEmbed]
            rfl

/-- The Amendment-6 closed form is compatible with the proved sharp
radius: `2^k ≤ 2^{k+1} − 2` for every `k ≥ 1` (FALSE at `k = 0`, where
the honest radius is the plaquette's unit extent — stated openly). -/
theorem kStep_radius_le_amendment {k : ℕ} (hk : 1 ≤ k) :
    2 ^ k ≤ 2 ^ (k + 1) - 2 := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hs : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  omega

/-- **THE k-STEP RADIUS BOUND, Amendment-6 form** (`r_k ≤ 2^{k+1} − 2`,
the corrected recursion's closed form, for `1 ≤ k`): the `k`-step
transported support sits inside the plane box of side `2^{k+1} − 2` at the
`2^k`-scaled anchor.  Derived from the sharp master bound `2^k`. -/
theorem kStepBlockSupport_radius (M₀ : ℕ) [NeZero M₀] (r : ℕ)
    (P : ConcretePlaquette d (towerSize M₀ r)) {k : ℕ} (hk : 1 ≤ k) :
    ∀ e ∈ kStepBlockSupport M₀ r (plaquetteSupport P) k,
      ∃ a b : ℕ, a ≤ 2 ^ (k + 1) - 2 ∧ b ≤ 2 ^ (k + 1) - 2 ∧
        e.1.source
          = shiftIter (shiftIter (iterEmbed M₀ r P.site k) P.dir1 a)
              P.dir2 b := by
  intro e he
  obtain ⟨-, a, b, ha, hb, hsrc⟩ :=
    kStepBlockSupport_source_in_ball M₀ r P k e he
  have ha' : a ≤ 2 ^ k := le_trans (Nat.le_add_right _ _) ha
  have hb' : b ≤ 2 ^ k := le_trans (Nat.le_add_right _ _) hb
  have hle := kStep_radius_le_amendment hk
  exact ⟨a, b, by omega, by omega, hsrc⟩

/-- Consistency with B-1'''': ONE tower step of the support transport IS
`blockPlaquetteSupport` — definitionally. -/
theorem kStepBlockSupport_one (M₀ : ℕ) [NeZero M₀] (r : ℕ)
    (P : ConcretePlaquette d (towerSize M₀ r)) :
    kStepBlockSupport M₀ r (plaquetteSupport P) 1
      = blockPlaquetteSupport P := rfl

end KStepRadius

/-! ### 4.  Item 2: the k-step canonical separation theorem -/

section KStepSeparation

variable {d : ℕ} [NeZero d]

/-- The leading coordinate of every `k`-step transported-support source of
a canonical plaquette: the `2^k`-scaled offset plus a slack of at most
`2^k`, modulo the fine torus size. -/
theorem kStepSupport_canonical_source_coord (hd : 2 ≤ d) (M₀ : ℕ)
    [NeZero M₀] (r τ k : ℕ) :
    ∀ e ∈ kStepBlockSupport M₀ r
        (plaquetteSupport (canonicalPlaquette d (towerSize M₀ r) hd τ)) k,
      ∃ a : ℕ, a ≤ 2 ^ k ∧
        (e.1.source (⟨0, by omega⟩ : Fin d)).val
          = (2 ^ k * (τ % towerSize M₀ r) + a) % towerSize M₀ (r + k) := by
  intro e he
  obtain ⟨-, a, b, ha, hb, hsrc⟩ := kStepBlockSupport_source_in_ball M₀ r
    (canonicalPlaquette d (towerSize M₀ r) hd τ) k e he
  have hd1 : (canonicalPlaquette d (towerSize M₀ r) hd τ).dir1
      = (⟨0, by omega⟩ : Fin d) := rfl
  have hd2 : (canonicalPlaquette d (towerSize M₀ r) hd τ).dir2
      = (⟨1, by omega⟩ : Fin d) := rfl
  rw [hd1, hd2] at hsrc
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ (⟨1, by omega⟩ : Fin d) :=
    Fin.ne_of_lt (Fin.mk_lt_mk.mpr Nat.zero_lt_one)
  have hbase : ((iterEmbed M₀ r
        (canonicalPlaquette d (towerSize M₀ r) hd τ).site k)
        (⟨0, by omega⟩ : Fin d)).val
      = 2 ^ k * (τ % towerSize M₀ r) := by
    rw [iterEmbed_coord, canonicalPlaquette_site_zero]
  refine ⟨a, le_trans (Nat.le_add_right _ _) ha, ?_⟩
  rw [hsrc, shiftIter_coord_other _ _ _ h01, shiftIter_coord_self, hbase]

/-- **THE k-STEP SUPPORT SEPARATION THEOREM (walk form), explicit slack
`2^k + 1`:** in the window `1 ≤ τ, 2τ ≤ M` (coarse size
`M = towerSize M₀ r` — this window CONTAINS the Amendment-6 window
`4τ ≤ M`, and it is exactly what the terminal tie at `τ = 2u`, `4u ≤ M₀`
needs), any fine plaquettes on the `2^k·M` torus whose supports meet the
two `k`-step transported supports of the canonical pair `(P₀, P_τ)` are
separated by at least `2^k·τ − (2^k + 1)` touch-steps: EVERY touch-walk
between them has at least that length.  Slack accounting: `2^k` = the
sharp transported-support radius (`kStepBlockSupport_source_in_ball`) +
`1` = one carrier-internal offset (`site_coord_zmod_of_mem_support`) —
the ZMod circular-potential argument of the one-step `c = 3` proof,
wrap-safe because the window keeps the residue strictly inside
`(0, 2^k·M)`.  At `τ = 1` the bound ℕ-truncates to `0` (vacuous-but-true,
dispatched separately); at `k = 1` this IS the B-1'''' constant `2τ − 3`
(`kStepSeparation_one`). -/
theorem kStepSupport_canonical_separation_walk (hd : 2 ≤ d) (M₀ : ℕ)
    [NeZero M₀] (r : ℕ) {τ : ℕ} (hτ : 1 ≤ τ)
    (hwin : 2 * τ ≤ towerSize M₀ r) (k : ℕ)
    {r₀ r₁ : ConcretePlaquette d (towerSize M₀ (r + k))}
    {e₀ e₁ : PosEdge d (towerSize M₀ (r + k))}
    (he₀r : e₀ ∈ plaquetteSupport r₀)
    (he₀s : e₀ ∈ kStepBlockSupport M₀ r
      (plaquetteSupport (canonicalPlaquette d (towerSize M₀ r) hd 0)) k)
    (he₁r : e₁ ∈ plaquetteSupport r₁)
    (he₁s : e₁ ∈ kStepBlockSupport M₀ r
      (plaquetteSupport (canonicalPlaquette d (towerSize M₀ r) hd τ)) k)
    (W : (touchGraph d (towerSize M₀ (r + k))).Walk r₀ r₁) :
    2 ^ k * τ - (2 ^ k + 1) ≤ W.length := by
  by_cases hτ1 : τ = 1
  · -- ℕ-truncation: at `τ = 1` the bound is `0` — trivially true.
    subst hτ1
    have h1 : 2 ^ k * 1 = 2 ^ k := mul_one _
    omega
  have hτ2 : 2 ≤ τ := by omega
  have hτM : τ < towerSize M₀ r := by omega
  have hNM : towerSize M₀ (r + k) = 2 ^ k * towerSize M₀ r := by
    rw [towerSize_eq_pow_mul, towerSize_eq_pow_mul, pow_add]
    ring
  have h2k : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hexp : 2 ^ k * (τ + 2) = 2 ^ k * τ + 2 ^ k + 2 ^ k := by ring
  have hτ2M : τ + 2 ≤ towerSize M₀ r := by omega
  have hlt : 2 ^ k * (τ + 2) ≤ towerSize M₀ (r + k) := by
    rw [hNM]
    exact Nat.mul_le_mul_left _ hτ2M
  obtain ⟨a₀, ha₀, hc₀⟩ :=
    kStepSupport_canonical_source_coord hd M₀ r 0 k e₀ he₀s
  obtain ⟨a₁, ha₁, hc₁⟩ :=
    kStepSupport_canonical_source_coord hd M₀ r τ k e₁ he₁s
  have hv₀ : (e₀.1.source (⟨0, by omega⟩ : Fin d)).val = a₀ := by
    rw [hc₀, Nat.zero_mod, Nat.mul_zero, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  have hv₁ : (e₁.1.source (⟨0, by omega⟩ : Fin d)).val = 2 ^ k * τ + a₁ := by
    rw [hc₁, Nat.mod_eq_of_lt hτM]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨δ₀, hδ₀, hz₀⟩ :=
    site_coord_zmod_of_mem_support he₀r (⟨0, by omega⟩ : Fin d)
  obtain ⟨δ₁, hδ₁, hz₁⟩ :=
    site_coord_zmod_of_mem_support he₁r (⟨0, by omega⟩ : Fin d)
  obtain ⟨J, hJ, hzW⟩ := walk_site_zmod W (⟨0, by omega⟩ : Fin d)
  rw [hv₀] at hz₀
  rw [hv₁] at hz₁
  have hdvd : ((towerSize M₀ (r + k) : ℕ) : ℤ)
      ∣ (2 ^ k * (τ : ℤ) + (a₁ : ℤ) + δ₀ - (a₀ : ℤ) - δ₁ - J) := by
    have hz : ((2 ^ k * (τ : ℤ) + (a₁ : ℤ) + δ₀ - (a₀ : ℤ) - δ₁ - J : ℤ) :
        ZMod (towerSize M₀ (r + k))) = 0 := by
      have h₀' : ((a₀ : ℕ) : ZMod (towerSize M₀ (r + k)))
          = (((r₀.site (⟨0, by omega⟩ : Fin d)).val : ℕ) :
              ZMod (towerSize M₀ (r + k)))
            + (δ₀ : ZMod (towerSize M₀ (r + k))) := hz₀
      have h₁' : ((2 ^ k * τ + a₁ : ℕ) : ZMod (towerSize M₀ (r + k)))
          = (((r₁.site (⟨0, by omega⟩ : Fin d)).val : ℕ) :
              ZMod (towerSize M₀ (r + k)))
            + (δ₁ : ZMod (towerSize M₀ (r + k))) := hz₁
      push_cast at h₀' h₁' ⊢
      linear_combination h₁' - h₀' + hzW
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ (towerSize M₀ (r + k))).mp hz
  by_contra hcon
  have hlen : W.length + 2 ^ k + 2 ≤ 2 ^ k * τ := by omega
  obtain ⟨q, hq⟩ := hdvd
  have hJ₁ : J ≤ (W.length : ℤ) := by omega
  have hJ₂ : -(W.length : ℤ) ≤ J := by omega
  have hlen' : (W.length : ℤ) + 2 ^ k + 2 ≤ 2 ^ k * (τ : ℤ) := by
    exact_mod_cast hlen
  have h2Tn : 2 * (2 ^ k * τ) ≤ towerSize M₀ (r + k) := by
    have h1 : 2 ^ k * (2 * τ) ≤ 2 ^ k * towerSize M₀ r :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : 2 ^ k * (2 * τ) = 2 * (2 ^ k * τ) := by ring
    omega
  have h2T : 2 * (2 ^ k * (τ : ℤ)) ≤ ((towerSize M₀ (r + k) : ℕ) : ℤ) := by
    exact_mod_cast h2Tn
  have ha₀' : (a₀ : ℤ) ≤ 2 ^ k := by exact_mod_cast ha₀
  have ha₁' : (a₁ : ℤ) ≤ 2 ^ k := by exact_mod_cast ha₁
  have ha₀0 : (0 : ℤ) ≤ (a₀ : ℤ) := Int.natCast_nonneg a₀
  have ha₁0 : (0 : ℤ) ≤ (a₁ : ℤ) := Int.natCast_nonneg a₁
  have hN0 : (0 : ℤ) < ((towerSize M₀ (r + k) : ℕ) : ℤ) := by
    exact_mod_cast NeZero.pos (towerSize M₀ (r + k))
  have hD1 : 1 ≤ ((towerSize M₀ (r + k) : ℕ) : ℤ) * q := by
    rw [← hq]
    rcases hδ₀ with rfl | rfl <;> rcases hδ₁ with rfl | rfl <;> linarith
  have hD2 : ((towerSize M₀ (r + k) : ℕ) : ℤ) * q
      < ((towerSize M₀ (r + k) : ℕ) : ℤ) := by
    rw [← hq]
    rcases hδ₀ with rfl | rfl <;> rcases hδ₁ with rfl | rfl <;> linarith
  have hq1 : 1 ≤ q := by
    by_contra hq0
    push_neg at hq0
    have hq0' : q ≤ 0 := by omega
    have hmul := mul_le_mul_of_nonneg_left hq0' hN0.le
    rw [mul_zero] at hmul
    linarith
  have hNq : ((towerSize M₀ (r + k) : ℕ) : ℤ)
      ≤ ((towerSize M₀ (r + k) : ℕ) : ℤ) * q :=
    le_mul_of_one_le_right hN0.le hq1
  linarith

/-- **k-step support separation, distance form:**
`2^k·τ − (2^k + 1) ≤ dist(r₀, r₁)` for any fine plaquettes whose supports
meet the two `k`-step transported supports (reachability required to make
`SimpleGraph.dist` meaningful). -/
theorem kStepSupport_canonical_separation_dist (hd : 2 ≤ d) (M₀ : ℕ)
    [NeZero M₀] (r : ℕ) {τ : ℕ} (hτ : 1 ≤ τ)
    (hwin : 2 * τ ≤ towerSize M₀ r) (k : ℕ)
    {r₀ r₁ : ConcretePlaquette d (towerSize M₀ (r + k))}
    (h₀ : ¬ Disjoint (plaquetteSupport r₀)
      (kStepBlockSupport M₀ r
        (plaquetteSupport (canonicalPlaquette d (towerSize M₀ r) hd 0)) k))
    (h₁ : ¬ Disjoint (plaquetteSupport r₁)
      (kStepBlockSupport M₀ r
        (plaquetteSupport (canonicalPlaquette d (towerSize M₀ r) hd τ)) k))
    (hreach : (touchGraph d (towerSize M₀ (r + k))).Reachable r₀ r₁) :
    2 ^ k * τ - (2 ^ k + 1)
      ≤ (touchGraph d (towerSize M₀ (r + k))).dist r₀ r₁ := by
  obtain ⟨e₀, he₀r, he₀s⟩ := Finset.not_disjoint_iff.mp h₀
  obtain ⟨e₁, he₁r, he₁s⟩ := Finset.not_disjoint_iff.mp h₁
  obtain ⟨W, hW⟩ := hreach.exists_walk_length_eq_dist
  have h := kStepSupport_canonical_separation_walk hd M₀ r hτ hwin k
    he₀r he₀s he₁r he₁s W
  omega

/-- At `k = 1` the k-step separation constant IS the proved one-step
constant: `2^1·τ − (2^1 + 1) = 2τ − 3`. -/
theorem kStepSeparation_one (τ : ℕ) :
    2 ^ 1 * τ - (2 ^ 1 + 1) = 2 * τ - 3 := by
  norm_num

/-- **THE POSITIVITY WINDOW, stated exactly:** for `τ ≥ 2` and `k ≥ 1` the
k-step separation lower bound is strictly positive.  (At `τ = 1` it
ℕ-truncates to `0`; at `k = 0` it is `τ − 2`, positive only from `τ ≥ 3` —
neither is claimed.) -/
theorem kStepSeparation_pos {τ : ℕ} (hτ : 2 ≤ τ) {k : ℕ} (hk : 1 ≤ k) :
    0 < 2 ^ k * τ - (2 ^ k + 1) := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hm : 2 ^ k * 2 ≤ 2 ^ k * τ := Nat.mul_le_mul_left _ hτ
  omega

/-- **Strict growth in the number of blocking steps:** on the positivity
window (`τ ≥ 2`, `k ≥ 1`) the k-step separation lower bound strictly
increases with `k`. -/
theorem kStepSeparation_strictMono {τ : ℕ} (hτ : 2 ≤ τ) {k : ℕ}
    (hk : 1 ≤ k) :
    2 ^ k * τ - (2 ^ k + 1) < 2 ^ (k + 1) * τ - (2 ^ (k + 1) + 1) := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hm : 2 ^ k * 2 ≤ 2 ^ k * τ := Nat.mul_le_mul_left _ hτ
  have hs : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  have hs' : 2 ^ (k + 1) * τ = 2 * (2 ^ k * τ) := by
    rw [hs]; ring
  omega

end KStepSeparation

/-! ### 5.  The terminal-stage tie: the k = kTerm n instance the gate
### consumes -/

section TerminalTie

variable {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]

/-- At the terminal stage the scale-corrected separation index reduces to
the renormalized index: `2^(n − kTerm n)·u = u` (because `kTerm n = n`). -/
theorem terminal_stage_sep_index (n u : ℕ) : 2 ^ (n - kTerm n) * u = u := by
  show 2 ^ (n - n) * u = u
  rw [Nat.sub_self, pow_zero, one_mul]

/-- The terminal stage lives on the BASE torus:
`towerSize M₀ (n − kTerm n) = M₀`. -/
theorem terminal_stage_size (M₀ n : ℕ) :
    towerSize M₀ (n - kTerm n) = M₀ := by
  have h : n - kTerm n = 0 := Nat.sub_self n
  rw [h, towerSize_zero]

/-- **THE TIE, definitional (`rfl`):** the terminal IR object consumed by
`TerminalScaleWilsonGate` AND `PhysicalTerminalScaleWilsonGate` — the
scaled canonical IR correlator at the syntactic index `fun _ => kTerm n` —
IS the truncated correlator of the `kTerm n`-fold blocked measure AT the
canonical plaquette pair `(P₀, P_{2·(2^{n−kTerm n}·u)})` on the
`towerSize M₀ (n − kTerm n)` torus (= the base torus `M₀`,
`terminal_stage_size`, at offset `2u`, `terminal_stage_sep_index`).  Same
term, no bridging freedom: the k-step support theorems below are about
EXACTLY this pair. -/
theorem terminalIR_is_canonical_pair_correlator (hd : 2 ≤ d) (M₀ : ℕ)
    [NeZero M₀] (n : ℕ) (μ : Measure (GaugeConfig d (towerSize M₀ n) G))
    (f : G → ℝ) (u : ℕ) :
    scaledCanonicalCovIR hd M₀ n μ f (fun _ => kTerm n) u
      = truncatedPlaquetteCorrelatorOfMeasure
          (towerMeasure M₀ n μ (kTerm n)) f
          (canonicalPlaquette d (towerSize M₀ (n - kTerm n)) hd 0)
          (canonicalPlaquette d (towerSize M₀ (n - kTerm n)) hd
            (2 * (2 ^ (n - kTerm n) * u))) := rfl

/-- **THE TERMINAL-STAGE SUPPORT SEPARATION (k = kTerm n, the instance the
gate consumes), walk form.**  The canonical pair of the terminal
correlator at gate separation index `u` is the offset-`2u` pair on the
base torus (`terminalIR_is_canonical_pair_correlator` +
`terminal_stage_sep_index`/`terminal_stage_size`); its `kTerm n`-step
transported supports on the size-`2^n·M₀` torus separate every pair of
touching carriers by `2^n·(2u) − (2^n + 1)` touch-steps.  THE WINDOW IS
THE GATE'S OWN WINDOW `1 ≤ u ∧ 4u ≤ M₀` — a condition on `(u, M₀)` ONLY,
INDEPENDENT of the depth `n` (`terminal_window_nonempty`: satisfiable at
every base `M₀ ≥ 4`, hence at every depth simultaneously). -/
theorem terminalSupport_canonical_separation_walk (hd : 2 ≤ d) (M₀ : ℕ)
    [NeZero M₀] (n : ℕ) {u : ℕ} (hu : 1 ≤ u) (h4 : 4 * u ≤ M₀)
    {r₀ r₁ : ConcretePlaquette d (towerSize M₀ (0 + kTerm n))}
    {e₀ e₁ : PosEdge d (towerSize M₀ (0 + kTerm n))}
    (he₀r : e₀ ∈ plaquetteSupport r₀)
    (he₀s : e₀ ∈ kStepBlockSupport M₀ 0
      (plaquetteSupport (canonicalPlaquette d M₀ hd 0)) (kTerm n))
    (he₁r : e₁ ∈ plaquetteSupport r₁)
    (he₁s : e₁ ∈ kStepBlockSupport M₀ 0
      (plaquetteSupport (canonicalPlaquette d M₀ hd (2 * u))) (kTerm n))
    (W : (touchGraph d (towerSize M₀ (0 + kTerm n))).Walk r₀ r₁) :
    2 ^ kTerm n * (2 * u) - (2 ^ kTerm n + 1) ≤ W.length := by
  have h1 : 1 ≤ 2 * u := by omega
  have hwin : 2 * (2 * u) ≤ M₀ := by omega
  exact kStepSupport_canonical_separation_walk hd M₀ 0 h1 hwin (kTerm n)
    he₀r he₀s he₁r he₁s W

/-- Terminal-stage support separation, distance form (same gate window,
independent of `n`). -/
theorem terminalSupport_canonical_separation_dist (hd : 2 ≤ d) (M₀ : ℕ)
    [NeZero M₀] (n : ℕ) {u : ℕ} (hu : 1 ≤ u) (h4 : 4 * u ≤ M₀)
    {r₀ r₁ : ConcretePlaquette d (towerSize M₀ (0 + kTerm n))}
    (h₀ : ¬ Disjoint (plaquetteSupport r₀)
      (kStepBlockSupport M₀ 0
        (plaquetteSupport (canonicalPlaquette d M₀ hd 0)) (kTerm n)))
    (h₁ : ¬ Disjoint (plaquetteSupport r₁)
      (kStepBlockSupport M₀ 0
        (plaquetteSupport (canonicalPlaquette d M₀ hd (2 * u))) (kTerm n)))
    (hreach : (touchGraph d (towerSize M₀ (0 + kTerm n))).Reachable r₀ r₁) :
    2 ^ kTerm n * (2 * u) - (2 ^ kTerm n + 1)
      ≤ (touchGraph d (towerSize M₀ (0 + kTerm n))).dist r₀ r₁ := by
  have h1 : 1 ≤ 2 * u := by omega
  have hwin : 2 * (2 * u) ≤ M₀ := by omega
  exact kStepSupport_canonical_separation_dist hd M₀ 0 h1 hwin (kTerm n)
    h₀ h₁ hreach

/-- **CONCRETE STRICT POSITIVITY AT k = kTerm n = n:** on the gate's own
depth range (`1 ≤ n`) and for EVERY window separation (`1 ≤ u` — the
canonical coarse offset is `τ = 2u ≥ 2`), the terminal-stage separation
lower bound is strictly positive.  The hypotheses mention only `n ≥ 1`
and `u ≥ 1`: no shrinking window in `n`. -/
theorem terminalSupport_separation_pos {n : ℕ} (hn : 1 ≤ n) {u : ℕ}
    (hu : 1 ≤ u) :
    0 < 2 ^ kTerm n * (2 * u) - (2 ^ kTerm n + 1) :=
  kStepSeparation_pos (by omega) (kTerm_pos hn)

/-- **STRICT GROWTH IN THE DEPTH:** the terminal-stage separation lower
bound strictly increases from depth `n` to depth `n + 1`
(`kTerm (n+1) = kTerm n + 1` definitionally). -/
theorem terminalSupport_separation_strict_growth {n : ℕ} (hn : 1 ≤ n)
    {u : ℕ} (hu : 1 ≤ u) :
    2 ^ kTerm n * (2 * u) - (2 ^ kTerm n + 1)
      < 2 ^ kTerm (n + 1) * (2 * u) - (2 ^ kTerm (n + 1) + 1) :=
  kStepSeparation_strictMono (by omega) (kTerm_pos hn)

/-- **The gate window is nonempty at every base `M₀ ≥ 4`, uniformly in the
depth:** the window condition `1 ≤ u ∧ 4u ≤ M₀` of the terminal-stage
separation theorems is a condition on `(u, M₀)` only — no `n` appears —
so it remains satisfiable (by the same `u`) as `n` grows. -/
theorem terminal_window_nonempty (M₀ : ℕ) (hM : 4 ≤ M₀) :
    ∃ u : ℕ, 1 ≤ u ∧ 4 * u ≤ M₀ :=
  ⟨1, le_refl 1, by omega⟩

end TerminalTie

end YangMills.RG
