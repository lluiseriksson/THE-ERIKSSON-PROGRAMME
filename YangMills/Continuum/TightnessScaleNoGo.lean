/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson, OpenAI Codex -/

import YangMills.L1_GibbsMeasure.TwoPlaquetteCorrelator

/-!
# Physical scale dictionary and the strong-coupling-window no-go

The existing lattice is dimensionless.  This file introduces only the minimal
physical dictionary needed to state an `a → 0` obligation, then proves that
the radius hypothesis used by the volume-uniform strong-coupling theorem has
a finite coupling cap.  Every trajectory with `β(a) → +∞` eventually leaves
that window.

This is a negative routing theorem.  It does not construct a continuum
measure and does not use the occupied RG/hRpoly producer.

Oracle target: no project axioms. No sorry.
-/

namespace YangMills.ContinuumC1

open Filter Set

/-- Lane-local dimensional contract.  `a` has dimension length and `g2`
has the physical dimension of the squared coupling. -/
structure ScaleDict where
  a : ℝ
  a_pos : 0 < a
  g2 : ℝ
  g2_pos : 0 < g2

namespace ScaleDict

/-- Physical length represented by `n` lattice steps. -/
def physicalLength (S : ScaleDict) (n : ℕ) : ℝ := S.a * n

/-- Physical area represented by `n` lattice plaquettes. -/
def physicalArea (S : ScaleDict) (n : ℕ) : ℝ := S.a ^ 2 * n

/-- Two-dimensional Wilson coupling convention used by the C1 positive
target: `β(a)=1/(g²a²)`. -/
noncomputable def beta2D (S : ScaleDict) : ℝ :=
  1 / (S.g2 * S.a ^ 2)

theorem beta2D_pos (S : ScaleDict) : 0 < S.beta2D := by
  unfold beta2D
  exact one_div_pos.mpr
    (mul_pos S.g2_pos (pow_pos S.a_pos 2))

end ScaleDict

/-- The binding radius hypothesis of the checked two-plaquette theorem at
`t=ε=1`. -/
def KPRadiusAtUnit (d N_c : ℕ) (β s : ℝ) : Prop :=
  ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
    (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
      (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
      Real.exp (1 + 1 + 1)) < 1

/-- Typed identification with the radius conjunct in the checked
`sun_clustering_window_nonempty` theorem. -/
theorem kpRadiusAtUnit_iff_checkedWindow (d Nc : ℕ) (β s : ℝ) :
    KPRadiusAtUnit d Nc β s ↔
      (((16 * d + 1 : ℕ) : ℝ) ^ 2 *
        (((Real.exp (|β| * (Nc : ℝ)) - 1) + s +
          (Real.exp (|β| * (Nc : ℝ)) - 1) * s) *
          Real.exp (1 + 1 + 1)) < 1) := by
  rfl

/-- The checked repository window supplies a positive-coupling witness for
`KPRadiusAtUnit`; the no-go is therefore not a statement about an empty
hypothesis.  This theorem is also the compile-time bridge to the producer. -/
theorem kpRadiusAtUnit_nonempty_from_checkedWindow
    (d Nc : ℕ) [NeZero Nc] :
    ∃ β s : ℝ, 0 < β ∧ 0 < s ∧ KPRadiusAtUnit d Nc β s := by
  obtain ⟨β₀, hβ₀, s, hs, hwindow⟩ :=
    YangMills.sun_clustering_window_nonempty d Nc
  have hβabs : |β₀| ≤ β₀ := by simp [abs_of_pos hβ₀]
  exact ⟨β₀, s, hβ₀, hs,
    (kpRadiusAtUnit_iff_checkedWindow d Nc β₀ s).2
      (hwindow β₀ hβabs).1⟩

/-- Partially apply the actual checked correlator theorem through its radius
argument. The remaining inferred function asks for `hsmall`, plaquettes,
distance, and `hone`. If the producer changes its radius hypothesis
incompatibly, this definition stops elaborating. -/
noncomputable def checkedCorrelatorAfterKPRadiusAtUnit
    {d N : ℕ} [NeZero d] [NeZero N]
    (Nc : ℕ) [NeZero Nc]
    {f : ↥(Matrix.specialUnitaryGroup (Fin Nc) ℂ) → ℝ}
    (hfm : Measurable f) (hf : ∀ x, |f x| ≤ 1)
    {s : ℝ} (hs0 : 0 < s) (β : ℝ)
    (hKP : KPRadiusAtUnit d Nc β s) :=
  YangMills.sun_two_plaquette_correlator_bound
    (d := d) (N := N) Nc hfm hf hs0 β 1 1
    (by norm_num) (by norm_num)
    ((kpRadiusAtUnit_iff_checkedWindow d Nc β s).1 hKP)

/-- Fully numerical non-vacuity witness at the four-dimensional
three-color parameters used in the audit. -/
theorem kpRadiusAtUnit_witness_4_3 :
    KPRadiusAtUnit 4 3 0 (1 / 200000) := by
  have he1le := Real.exp_bound' (x := (1 : ℝ))
    (by norm_num) (by norm_num) (n := 3) (by norm_num)
  have he1 : Real.exp 1 < 3 := by
    calc
      Real.exp 1 ≤
          (∑ m ∈ Finset.range 3, (1 : ℝ) ^ m / m.factorial) +
            (1 : ℝ) ^ 3 * (3 + 1) / (Nat.factorial 3 * 3) := by
              simpa using he1le
      _ < 3 := by norm_num [Finset.sum_range_succ, Nat.factorial]
  have he3 : Real.exp 3 < 27 := by
    have hfactor :
        0 < (3 - Real.exp 1) *
          (9 + 3 * Real.exp 1 + (Real.exp 1) ^ 2) := by
      apply mul_pos (sub_pos.mpr he1)
      nlinarith [sq_nonneg (Real.exp 1)]
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num,
      Real.exp_add, Real.exp_add]
    nlinarith
  unfold KPRadiusAtUnit
  norm_num [Real.exp_zero]
  nlinarith

/-- Necessary supremum of the `t=ε=1` KP radius window as `s ↓ 0`. -/
noncomputable def kpBetaCap (d Nc : ℕ) : ℝ :=
  Real.log
      (1 + 1 /
        (((((16 * d + 1 : ℕ) : ℝ) ^ 2) * Real.exp 3))) /
    (Nc : ℝ)

theorem kpBetaCap_pos (d Nc : ℕ) (hNc : 0 < Nc) :
    0 < kpBetaCap d Nc := by
  unfold kpBetaCap
  have hK : (0 : ℝ) <
      ((((16 * d + 1 : ℕ) : ℝ) ^ 2) * Real.exp 3) := by
    positivity
  have hlog : 0 < Real.log (1 + 1 /
      ((((16 * d + 1 : ℕ) : ℝ) ^ 2) * Real.exp 3)) := by
    apply Real.log_pos
    have : 0 < 1 /
        ((((16 * d + 1 : ℕ) : ℝ) ^ 2) * Real.exp 3) := by
      positivity
    linarith
  exact div_pos hlog (by exact_mod_cast hNc)

/-- **Finite-window theorem.**  The actual KP radius hypothesis, with any
strictly positive deformation `s`, forces `β` below the explicit finite cap.
-/
theorem beta_lt_kpBetaCap
    (d Nc : ℕ) (hNc : 0 < Nc)
    (β s : ℝ) (hβ : 0 ≤ β) (hs : 0 < s)
    (hKP : KPRadiusAtUnit d Nc β s) :
    β < kpBetaCap d Nc := by
  let C : ℝ :=
    ((((16 * d + 1 : ℕ) : ℝ) ^ 2) * Real.exp 3)
  let w : ℝ := Real.exp (β * (Nc : ℝ)) - 1
  have hNcR : (0 : ℝ) < (Nc : ℝ) := by exact_mod_cast hNc
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hw0 : 0 ≤ w := by
    dsimp [w]
    have : (1 : ℝ) ≤ Real.exp (β * (Nc : ℝ)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hβ hNcR.le)
    linarith
  have hactivity : w < w + s + w * s := by
    nlinarith [mul_nonneg hw0 hs.le]
  have hKP' : C * (w + s + w * s) < 1 := by
    have hthree : (1 + 1 + 1 : ℝ) = 3 := by norm_num
    simpa [KPRadiusAtUnit, C, w, hthree, abs_of_nonneg hβ, mul_assoc,
      mul_left_comm, mul_comm] using hKP
  have hCw : C * w < 1 :=
    (mul_lt_mul_of_pos_left hactivity hC).trans hKP'
  have hw : w < 1 / C := by
    apply (lt_div_iff₀ hC).2
    simpa [mul_comm] using hCw
  have hexp : Real.exp (β * (Nc : ℝ)) < 1 + 1 / C := by
    dsimp [w] at hw
    linarith
  have harg : 0 < 1 + 1 / C := by positivity
  have hlog : β * (Nc : ℝ) < Real.log (1 + 1 / C) := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log harg]
    exact hexp
  rw [kpBetaCap]
  change β < Real.log (1 + 1 / C) / (Nc : ℝ)
  exact (lt_div_iff₀ hNcR).2 hlog

/-- The explicit two-dimensional trajectory leaves the KP radius window as
soon as `g² a² β_cap ≤ 1`. -/
theorem not_kpRadiusAtUnit_beta2D
    (d Nc : ℕ) (hNc : 0 < Nc)
    (S : ScaleDict) (s : ℝ) (hs : 0 < s)
    (hsmall : S.g2 * S.a ^ 2 * kpBetaCap d Nc ≤ 1) :
    ¬ KPRadiusAtUnit d Nc S.beta2D s := by
  intro hKP
  have hβpos := S.beta2D_pos
  have hlt :=
    beta_lt_kpBetaCap d Nc hNc S.beta2D s hβpos.le hs hKP
  have hden : 0 < S.g2 * S.a ^ 2 :=
    mul_pos S.g2_pos (pow_pos S.a_pos 2)
  have hcaple : kpBetaCap d Nc ≤ S.beta2D := by
    unfold ScaleDict.beta2D
    apply (le_div_iff₀ hden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsmall
  exact (not_lt_of_ge hcaple) hlt

/-- **Structural no-go.**  Any coupling trajectory tending to `+∞`
eventually violates the checked strong-coupling radius hypothesis. -/
theorem eventually_not_kpRadiusAtUnit_of_tendsto
    {ι : Type*} (l : Filter ι) (β : ι → ℝ)
    (d Nc : ℕ) (hNc : 0 < Nc) (s : ℝ) (hs : 0 < s)
    (hβ : Tendsto β l atTop) :
    ∀ᶠ i in l, ¬ KPRadiusAtUnit d Nc (β i) s := by
  have hcap := kpBetaCap_pos d Nc hNc
  have hev : ∀ᶠ i in l, kpBetaCap d Nc ≤ β i :=
    hβ (eventually_ge_atTop (kpBetaCap d Nc))
  filter_upwards [hev] with i hi hKP
  have hlt :=
    beta_lt_kpBetaCap d Nc hNc (β i) s
      (hcap.le.trans hi) hs hKP
  exact (not_lt_of_ge hi) hlt

/-- The endpoint `a=1`, `g²=1` of the concrete family `0<a≤1`. Since the
threshold hypothesis is `g²a² β_cap≤1`, this endpoint is the hardest member;
every smaller positive `a` satisfies the same inequality a fortiori. -/
noncomputable def unitScale : ScaleDict where
  a := 1
  a_pos := by norm_num
  g2 := 1
  g2_pos := by norm_num

theorem unitScale_kpCap_small :
    unitScale.g2 * unitScale.a ^ 2 * kpBetaCap 4 3 ≤ 1 := by
  have hden : (1 : ℝ) ≤ 4225 * Real.exp 3 := by
    have he : (1 : ℝ) ≤ Real.exp 3 :=
      Real.one_le_exp (by norm_num)
    nlinarith
  have hinv : 1 / (4225 * Real.exp 3) ≤ (1 : ℝ) := by
    exact (div_le_one (by positivity)).2 hden
  have hlog := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < 1 + 1 / (4225 * Real.exp 3) by positivity)
  have hlogle :
      Real.log (1 + 1 / (4225 * Real.exp 3)) ≤ 1 := by
    have hlog' :
        Real.log (1 + 1 / (4225 * Real.exp 3)) ≤
          1 / (4225 * Real.exp 3) := by
      simpa only [add_sub_cancel_left] using hlog
    exact hlog'.trans hinv
  have hcap :
      Real.log (1 + 1 / (4225 * Real.exp 3)) / 3 ≤ 1 := by
    nlinarith
  have h65 : (65 : ℝ) ^ 2 = 4225 := by norm_num
  simpa [unitScale, kpBetaCap, h65] using hcap

end YangMills.ContinuumC1

#print axioms YangMills.ContinuumC1.kpRadiusAtUnit_nonempty_from_checkedWindow
#print axioms YangMills.ContinuumC1.checkedCorrelatorAfterKPRadiusAtUnit
#print axioms YangMills.ContinuumC1.kpRadiusAtUnit_witness_4_3
#print axioms YangMills.ContinuumC1.beta_lt_kpBetaCap
#print axioms YangMills.ContinuumC1.not_kpRadiusAtUnit_beta2D
#print axioms YangMills.ContinuumC1.eventually_not_kpRadiusAtUnit_of_tendsto
#print axioms YangMills.ContinuumC1.unitScale_kpCap_small
