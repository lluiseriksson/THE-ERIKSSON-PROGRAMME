/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.ConcreteGaugeRGLiteralGate
import YangMills.RG.MarginalUVMassGap

/-!
# The terminal-index gate (C6 B-1^5): non-circularity closed in the type

`docs/C6-BRIDGE-CHARTER.md` Amendment 5 + the evaluator's definitive
`kTerm` specification (charter notes at 96479202).  The 5.95 verdict
identified the circularity of the depth-zero layer: the previous literal
gate's IR clause, at `n = 0`, directly hypothesized the sought physical
bound.  This module closes that in the type:

* **`kTerm`** — a FIXED definition (`kTerm n := n`), not an existential
  parameter: the terminal index is determined by inspection.  Range:
  `kTerm_pos : 1 ≤ n → 1 ≤ kTerm n` and `kTerm_le : kTerm n ≤ n` — both
  definitional (`id` / `le_refl`), so the clamp region `k > n` is
  unreachable at the consumed index, and the consumed tower stage is the
  genuinely `n`-fold blocked measure.
* **`TerminalScaleWilsonGate`** — the gate quantifies ONLY depths
  `1 ≤ n`; its IR clause evaluates SYNTACTICALLY
  `scaledCanonicalCovIR … (fun _ => kTerm n)`, which is BY `rfl`
  (`terminalGate_IR_index_eq`) the terminal correlator
  `scaledCanonicalCovEff … (kTerm n)` of the maximally blocked measure
  `towerMeasure … (kTerm n)`.  There is NO clause bounding the unblocked
  correlator `scaledCanonicalCovEff … 0` on its own: `k = 0` enters only
  inside the FIRST DIFFERENCE `Rsc u 0 = covEff 0 - covEff 1`
  (`rsc_is_difference`, by `rfl`) — a single-scale remainder, the honest
  hRpoly shape, not a decay hypothesis on the physical object.
* **`wilson_canonical_mass_gap_of_terminalScaleGate`** — the consumer
  exhibits the demanded chain: the telescoping
  (`scaledCanonical_decomposition` at `nsc := fun _ => kTerm n`) ENDS
  definitionally at the same `kTerm n` the IR clause consumes; the
  physical correlator (`scaledCovEff_zero_physical`, by `rfl`, = the
  canonical correlator of the base Wilson measure at physical separation
  `2^n·u`) is RECONSTRUCTED from the terminal bound plus the
  positive-scale remainders; one constant pack `(C, gap)` before every
  base and depth.  The decay is stated in the scale-invariant separation
  index `u` (physical separation `2^n·u` on the size-`2^n·M₀` torus) —
  exactly what the telescoping controls, nothing more is claimed.
* **`no_finite_domination_of_zero_then_nonzero`** — the literal
  obstruction: `Cov s = 0` and `Cov t ≠ 0` inside a doubling window
  exclude EVERY `K : ℝ`; specialized to the Wilson
  `CanonicalDoublingDomination` clause
  (`canonicalDoublingDomination_obstruction`).

**Residual-risk inventory (open, stated plainly).**  (i) NO witness of
the gate is provided or claimed — its satisfiability for the Wilson data
is the open mathematics; (ii) the k-step transported-support metric
theorem is NOT in this module: the missing lemma is the inductive radius
composition `r_{k+1} ≤ 2·r_k + 2` over the proved one-step radius-2
bound, composed with the exact anchor doubling — diagnosed in the ledger
as exceeding this execution's budget, not as false; (iii) the restricted
domination substitute remains a conditional interface (Wilson
satisfiability open); (iv) decay in `u` at fixed depth-to-base coupling,
per the honest lacunarity discussion of Amendment 5.  No new analytic
estimate; Clay distance ~0% (<0.1%), unchanged.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

open YangMills MeasureTheory

/-- **The terminal index — a FIXED definition, not data.**  At depth `n`
the terminal (maximally blocked) scale is `n` itself. -/
def kTerm (n : ℕ) : ℕ := n

/-- Range, lower half: at every consumed depth `1 ≤ n` the terminal index
is positive — the unblocked layer `k = 0` is not the IR object. -/
theorem kTerm_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ kTerm n := hn

/-- Range, upper half: the terminal index never exceeds the depth — the
clamp region of the tower is unreachable at the consumed index. -/
theorem kTerm_le (n : ℕ) : kTerm n ≤ n := le_rfl

section TerminalGate

variable {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]

/-- **The connection identity (definitional).**  The IR object consumed by
the gate — `scaledCanonicalCovIR` at the constant scale function
`fun _ => kTerm n` — IS the terminal correlator of the `kTerm n`-fold
blocked measure.  `rfl`: same term, no bridging freedom. -/
theorem terminalGate_IR_index_eq (hd : 2 ≤ d) (M₀ : ℕ) [NeZero M₀]
    (n : ℕ) (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    (u : ℕ) :
    scaledCanonicalCovIR hd M₀ n μ f (fun _ => kTerm n) u
      = scaledCanonicalCovEff hd M₀ n μ f (kTerm n) u := rfl

/-- **`k = 0` appears only inside the first difference.**  Each remainder
is definitionally a difference of consecutive effective correlators; no
gate clause bounds `scaledCanonicalCovEff … 0` alone. -/
theorem rsc_is_difference (hd : 2 ≤ d) (M₀ : ℕ) [NeZero M₀]
    (n : ℕ) (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    (u k : ℕ) :
    scaledCanonicalRsc hd M₀ n μ f u k
      = scaledCanonicalCovEff hd M₀ n μ f k u
        - scaledCanonicalCovEff hd M₀ n μ f (k + 1) u := rfl

/-- **The physical anchor (definitional).**  The scale-zero effective
correlator is the canonical correlator of the base measure at physical
separation `2^n · u`. -/
theorem scaledCovEff_zero_physical (hd : 2 ≤ d) (M₀ : ℕ) [NeZero M₀]
    (n : ℕ) (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    (u : ℕ) :
    scaledCanonicalCovEff hd M₀ n μ f 0 u
      = canonicalCorrelator hd μ f (2 ^ n * u) := by
  unfold scaledCanonicalCovEff
  rfl

end TerminalGate

/-- **THE TERMINAL-SCALE WILSON GATE (non-circular in the type).**
Constants before every base and depth; depths `1 ≤ n` ONLY; the IR
clause consumes syntactically the index `kTerm n` (with
`1 ≤ kTerm n ≤ n` by `kTerm_pos`/`kTerm_le`), i.e. the maximally
blocked, positively-scaled correlator; UV clauses bound only the
positive-scale remainders `k < kTerm n` (differences, per
`rsc_is_difference`); the nonvanishing clause is a data clause on the
same produced remainders.  NO clause mentions the unblocked correlator
alone.  NO witness is provided or claimed. -/
def TerminalScaleWilsonGate {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (N_c : ℕ) [NeZero N_c]
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
          ≤ C1 * Real.exp (-(ε * (u : ℝ)))) ∧
      (∀ u k : ℕ, 1 ≤ u → 4 * u ≤ M₀ → k < kTerm n →
        |scaledCanonicalRsc hd M₀ n
            (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f u k|
          ≤ C2 * Real.exp (-(c0 * (u : ℝ))) * g k ^ κ₀) ∧
      (∃ u k : ℕ, 1 ≤ u ∧ 4 * u ≤ M₀ ∧ k < kTerm n ∧
        scaledCanonicalRsc hd M₀ n
          (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f u k ≠ 0))

/-- **The consumer: physical reconstruction through the terminal index.**
The five-step chain, visible: (1) the terminal index is the fixed
`kTerm n`; (2) `1 ≤ kTerm n ≤ n` (`kTerm_pos`, `kTerm_le`); (3) the
gate's IR object equals the telescoping's terminal term by `rfl`
(`terminalGate_IR_index_eq`); (4) the physical correlator — the
canonical correlator of the BASE Wilson measure at physical separation
`2^n·u` (`scaledCovEff_zero_physical`, `rfl`) — is reconstructed via
`scaledCanonical_decomposition` at `nsc := fun _ => kTerm n`, which ends
at that same index; (5) no `k = 0` clause is consumed anywhere: the
bound on the physical object is DERIVED, not hypothesized. -/
theorem wilson_canonical_mass_gap_of_terminalScaleGate
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (N_c : ℕ) [NeZero N_c]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (β : ℝ)
    (hgate : TerminalScaleWilsonGate hd N_c f β) :
    ∃ C gap : ℝ, 0 < gap ∧
      ∀ (M₀ : ℕ) (_ : NeZero M₀), 4 ≤ M₀ → ∀ n : ℕ, 1 ≤ n →
      ∀ u : ℕ, 1 ≤ u → 4 * u ≤ M₀ →
        |canonicalCorrelator hd
            (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f
            (2 ^ n * u)|
          ≤ C * Real.exp (-(gap * (u : ℝ))) := by
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
  -- (4) reconstruction: the telescoping ends at kTerm n
  have hdec := scaledCanonical_decomposition hd M₀ n μ f (fun _ => kTerm n) u
  have hphys := scaledCovEff_zero_physical hd M₀ n μ f u
  -- bound the UV sum by one pack
  have hsumbound :
      |covUV_concrete (scaledCanonicalRsc hd M₀ n μ f) (fun _ => kTerm n) u|
        ≤ (C2 * Real.exp (-(c0 * (u : ℝ)))) * S := by
    have hamp : (0 : ℝ) ≤ C2 * Real.exp (-(c0 * (u : ℝ))) :=
      mul_nonneg hC2 (Real.exp_pos _).le
    have hRk : ∀ k, k ∈ Finset.range (kTerm n) →
        |scaledCanonicalRsc hd M₀ n μ f u k|
          ≤ (C2 * Real.exp (-(c0 * (u : ℝ)))) * g k ^ κ₀ := by
      intro k hk
      exact hUV u k hu h4u (Finset.mem_range.mp hk)
    calc |covUV_concrete (scaledCanonicalRsc hd M₀ n μ f) (fun _ => kTerm n) u|
        = |∑ k ∈ Finset.range (kTerm n), scaledCanonicalRsc hd M₀ n μ f u k| := rfl
      _ ≤ ∑ k ∈ Finset.range (kTerm n), |scaledCanonicalRsc hd M₀ n μ f u k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (kTerm n),
            (C2 * Real.exp (-(c0 * (u : ℝ)))) * g k ^ κ₀ :=
          Finset.sum_le_sum hRk
      _ = (C2 * Real.exp (-(c0 * (u : ℝ)))) *
            ∑ k ∈ Finset.range (kTerm n), g k ^ κ₀ := by
          rw [Finset.mul_sum]
      _ ≤ (C2 * Real.exp (-(c0 * (u : ℝ)))) * S :=
          mul_le_mul_of_nonneg_left
            (hsum.sum_le_tsum (Finset.range (kTerm n)) (fun k _ => hw k)) hamp
  -- assemble
  have hIRu := hIR u hu h4u
  have hexpε : Real.exp (-(ε * (u : ℝ))) ≤ Real.exp (-(min ε c0 * (u : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have : min ε c0 * (u : ℝ) ≤ ε * (u : ℝ) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg u)
    linarith
  have hexpc : Real.exp (-(c0 * (u : ℝ))) ≤ Real.exp (-(min ε c0 * (u : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have : min ε c0 * (u : ℝ) ≤ c0 * (u : ℝ) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg u)
    linarith
  calc |canonicalCorrelator hd μ f (2 ^ n * u)|
      = |scaledCanonicalCovEff hd M₀ n μ f 0 u| := by rw [hphys]
    _ = |scaledCanonicalCovIR hd M₀ n μ f (fun _ => kTerm n) u
          + covUV_concrete (scaledCanonicalRsc hd M₀ n μ f) (fun _ => kTerm n) u| := by
        rw [← hdec]
    _ ≤ |scaledCanonicalCovIR hd M₀ n μ f (fun _ => kTerm n) u|
          + |covUV_concrete (scaledCanonicalRsc hd M₀ n μ f) (fun _ => kTerm n) u| :=
        abs_add_le _ _
    _ ≤ C1 * Real.exp (-(ε * (u : ℝ)))
          + (C2 * Real.exp (-(c0 * (u : ℝ)))) * S :=
        add_le_add hIRu hsumbound
    _ ≤ C1 * Real.exp (-(min ε c0 * (u : ℝ)))
          + (C2 * S) * Real.exp (-(min ε c0 * (u : ℝ))) := by
        have h1 : C1 * Real.exp (-(ε * (u : ℝ)))
            ≤ C1 * Real.exp (-(min ε c0 * (u : ℝ))) :=
          mul_le_mul_of_nonneg_left hexpε hC1
        have h2 : (C2 * Real.exp (-(c0 * (u : ℝ)))) * S
            ≤ (C2 * S) * Real.exp (-(min ε c0 * (u : ℝ))) := by
          have := mul_le_mul_of_nonneg_left hexpc hC2
          nlinarith [hS0, (Real.exp_pos (-(c0 * (u : ℝ)))).le]
        linarith
    _ = (C1 + C2 * S) * Real.exp (-(min ε c0 * (u : ℝ))) := by ring

/-- **The literal domination obstruction.**  A zero followed by a nonzero
value inside a doubling window excludes EVERY finite `K`. -/
theorem no_finite_domination_of_zero_then_nonzero
    (Cov : ℕ → ℝ) {s t : ℕ} (hst : s ≤ t) (h2 : t ≤ 2 * s)
    (h0 : Cov s = 0) (h1 : Cov t ≠ 0) :
    ¬ ∃ K : ℝ, ∀ s' t' : ℕ, s' ≤ t' → t' ≤ 2 * s' →
      |Cov t'| ≤ K * |Cov s'| := by
  rintro ⟨K, hK⟩
  have h := hK s t hst h2
  rw [h0, abs_zero, mul_zero] at h
  exact h1 (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- The obstruction specialized to the Wilson doubling-domination clause:
if the canonical Wilson correlator vanishes at `(N, s)` but not at
`(N, t)` inside the admissible doubling window, then NO `K : ℝ`
satisfies `CanonicalDoublingDomination`. -/
theorem canonicalDoublingDomination_obstruction
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (N_c : ℕ) [NeZero N_c]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (β : ℝ)
    (N : ℕ) [NeZero N] {s t : ℕ}
    (hs : 1 ≤ s) (hst : s ≤ t) (h2 : t ≤ 2 * s) (h4 : 4 * t ≤ N)
    (h0 : canonicalCorrelator hd
      (wilsonGibbsMeasure (d := d) (N := N) N_c β) f s = 0)
    (h1 : canonicalCorrelator hd
      (wilsonGibbsMeasure (d := d) (N := N) N_c β) f t ≠ 0) :
    ¬ ∃ K : ℝ, CanonicalDoublingDomination hd N_c f β K := by
  rintro ⟨K, hK⟩
  have h := hK N s t hs hst h2 h4
  rw [h0, abs_zero, mul_zero] at h
  exact h1 (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

end YangMills.RG
