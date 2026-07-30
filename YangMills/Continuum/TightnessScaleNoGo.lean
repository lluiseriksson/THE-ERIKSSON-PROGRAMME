/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson, OpenAI Codex -/

import Mathlib

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
def KPRadiusAtUnit (d Nc : ℕ) (β s : ℝ) : Prop :=
  ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * (Nc : ℝ)) - 1) + s +
        (Real.exp (|β| * (Nc : ℝ)) - 1) * s) *
      Real.exp 3 < 1

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
    simpa [KPRadiusAtUnit, C, w, abs_of_nonneg hβ, mul_assoc,
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

end YangMills.ContinuumC1

#print axioms YangMills.ContinuumC1.beta_lt_kpBetaCap
#print axioms YangMills.ContinuumC1.not_kpRadiusAtUnit_beta2D
#print axioms YangMills.ContinuumC1.eventually_not_kpRadiusAtUnit_of_tendsto
