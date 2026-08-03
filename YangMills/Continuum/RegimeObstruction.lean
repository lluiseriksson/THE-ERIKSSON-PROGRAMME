/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.ThermodynamicLimit

/-!
# A quantitative obstruction inside the available KP regime

The repository's constructed infinite-volume states require a
`UniformLocalKPRegime`.  This module records a hard consequence of that
interface: for positive plaquette bound `B`, the coupling is uniformly
bounded.  In dimension four with `B = 2`, the bound is `|β| < 1 / 8450`.

Consequently, a coupling schedule tending to `+∞` cannot remain in this
regime.  This does not disprove a continuum limit; it precisely says that the
current strong-coupling thermodynamic producer cannot supply the
asymptotically-free scaling lane.
-/

namespace YangMills
namespace WindowPolymer

open Filter Topology

/-- The radius inequality in a uniform local KP regime forces a quantitative
upper bound on the absolute coupling. -/
theorem UniformLocalKPRegime.abs_beta_lt
    {d : ℕ} [NeZero d] {B β : ℝ}
    (hB : 0 < B) (κ : UniformLocalKPRegime d B β) :
    |β| <
      1 / ((((16 * d + 1 : ℕ) : ℝ) ^ 2) * B) := by
  let C : ℝ := (((16 * d + 1 : ℕ) : ℝ) ^ 2)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hx : 0 ≤ |β| * B :=
    mul_nonneg (abs_nonneg β) hB.le
  have hexp :
      |β| * B ≤ Real.exp (|β| * B) - 1 := by
    have h := Real.add_one_le_exp (|β| * B)
    linarith
  have hexp_nonneg : 0 ≤ Real.exp (|β| * B) - 1 :=
    hx.trans hexp
  have htilt : 1 ≤ Real.exp (κ.t + κ.ε) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith [κ.t_nonneg, κ.ε_pos])
  have hproduct :
      C * (|β| * B) < 1 := by
    calc
      C * (|β| * B) ≤ C * (Real.exp (|β| * B) - 1) :=
        mul_le_mul_of_nonneg_left hexp hC.le
      _ ≤ C *
          ((Real.exp (|β| * B) - 1) * Real.exp (κ.t + κ.ε)) :=
        mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_right hexp_nonneg htilt) hC.le
      _ < 1 := by
        simpa [C] using κ.radius_tilt
  apply (lt_div_iff₀ (mul_pos hC hB)).2
  calc
    |β| * (C * B) = C * (|β| * B) := by ring
    _ < 1 := hproduct

/-- In the four-dimensional `B = 2` interface used by the concrete SU(2)
witness, every admissible coupling satisfies `|β| < 1 / 8450`. -/
theorem UniformLocalKPRegime.abs_beta_lt_d4_two
    {β : ℝ} (κ : UniformLocalKPRegime 4 2 β) :
    |β| < 1 / 8450 := by
  have h := κ.abs_beta_lt (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

/-- No schedule tending to `+∞` can be supplied pointwise by the existing
four-dimensional `B = 2` uniform KP regime. -/
theorem no_asymptotically_free_scaling_in_KP_regime
    (β : ℕ → ℝ) (hβtop : Tendsto β atTop atTop) :
    ¬ ∀ n, Nonempty (UniformLocalKPRegime 4 2 (β n)) := by
  intro hregime
  have hevent : ∀ᶠ n in atTop, (1 : ℝ) ≤ β n :=
    (tendsto_atTop.1 hβtop) 1
  rcases hevent.exists with ⟨n, hn⟩
  let κ := Classical.choice (hregime n)
  have hbound : |β n| < (1 / 8450 : ℝ) :=
    κ.abs_beta_lt_d4_two
  have habs_lt_one : |β n| < (1 : ℝ) :=
    hbound.trans (by norm_num)
  exact
    (not_lt_of_ge (le_abs_self (β n)))
      (habs_lt_one.trans_le hn)

end WindowPolymer
end YangMills
