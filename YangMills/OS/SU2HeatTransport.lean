/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Lean2dYangMills.SU2HeatSemigroup
import YangMills.OS.SU2TransportWitness
import YangMills.OS.TransferGap

/-!
# Exact SU(2) heat-mode transport

The two-dimensional satellite proves the concrete infinite SU(2) heat kernel,
normalized-Haar character convolution and its semigroup law.  This module adds
the spectral statement needed by the parent transport programme: every actual
SU(2) Chebyshev character is an eigenfunction of heat convolution, and the
fundamental character is the sharp slowest non-vacuum mode.

Nothing below assumes an eigenvalue, a covariance bound, or an operator gap.
The eigenfunction identity is obtained by integrating finite heat-kernel sums
and passing to the infinite kernel by dominated convergence.

The finite Dobrushin witness remains a finite interface object.  The bridge at
the end identifies its rate with the eigenvalue of the genuine Haar-integral
heat operator; it does not assert that SU(2) itself is finite.
-/

noncomputable section

namespace YangMills.OS.SU2HeatTransport

open Finset Matrix MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

abbrev SU2 := Lean2dYangMills.SU2

/-! ## 1. Finite and infinite heat convolution on one character -/

/-- A finite heat-kernel partial sum acts diagonally on every character already
present in the sum.  This is an actual normalized-Haar convolution identity. -/
theorem heatKernelPartial_character_eigen_of_lt
    (N : ℕ) (t : ℝ) (m : ℕ) (hm : m < N) (g : SU2) :
    Lean2dYangMills.su2Convolution
        (Lean2dYangMills.su2HeatKernelPartial N t)
        (Lean2dYangMills.su2CharacterChebyshev m) g =
      Lean2dYangMills.su2ClassHeatWeight t m *
        Lean2dYangMills.su2CharacterChebyshev m g := by
  let a : ℕ → SU2 → ℂ := fun n x =>
    (((n : ℂ) + 1) * Lean2dYangMills.su2ClassHeatWeight t n) *
      Lean2dYangMills.su2CharacterChebyshev n x
  have ha (n : ℕ) : Integrable
      (fun x : SU2 =>
        a n x * Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g))
      Lean2dYangMills.su2HaarProb := by
    apply Lean2dYangMills.integrable_continuous_su2Haar
    dsimp [a]
    exact
      (continuous_const.mul
        (Lean2dYangMills.continuous_su2CharacterChebyshev n)).mul
        ((Lean2dYangMills.continuous_su2CharacterChebyshev m).comp <| by
          fun_prop)
  have hint (n : ℕ) :
      (∫ x : SU2,
        a n x * Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g)
          ∂Lean2dYangMills.su2HaarProb) =
        if n = m then
          Lean2dYangMills.su2ClassHeatWeight t m *
            Lean2dYangMills.su2CharacterChebyshev m g
        else 0 := by
    rw [show
      (fun x : SU2 =>
        a n x * Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g)) =
      fun x =>
        (((n : ℂ) + 1) * Lean2dYangMills.su2ClassHeatWeight t n) *
          (Lean2dYangMills.su2CharacterChebyshev n x *
            Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g)) by
        funext x
        dsimp [a]
        ring]
    calc
      (∫ x : SU2,
          (((n : ℂ) + 1) * Lean2dYangMills.su2ClassHeatWeight t n) *
            (Lean2dYangMills.su2CharacterChebyshev n x *
              Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g))
            ∂Lean2dYangMills.su2HaarProb) =
          (((n : ℂ) + 1) * Lean2dYangMills.su2ClassHeatWeight t n) *
            Lean2dYangMills.su2Convolution
              (Lean2dYangMills.su2CharacterChebyshev n)
              (Lean2dYangMills.su2CharacterChebyshev m) g :=
        MeasureTheory.integral_const_mul _ _
      _ = _ := by
        rw [Lean2dYangMills.su2CharacterChebyshev_convolution]
        split_ifs with hnm
        · subst n
          field_simp
        · simp
  rw [Lean2dYangMills.su2Convolution]
  simp_rw [Lean2dYangMills.su2HeatKernelPartial_eq_sum]
  change
    (∫ x : SU2,
      (∑ n ∈ Finset.range N, a n x) *
        Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g)
        ∂Lean2dYangMills.su2HaarProb) = _
  simp_rw [Finset.sum_mul]
  rw [MeasureTheory.integral_finset_sum (Finset.range N)
    (fun n _ => ha n)]
  simp_rw [hint]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl]
  · intro n hn hnm
    rw [if_neg hnm]
  · exact fun hnot => (hnot (Finset.mem_range.mpr hm)).elim

/-- **Concrete infinite heat-mode theorem.**  Normalized-Haar convolution by
the actual infinite SU(2) heat kernel sends the `m`-th character to its exact
Casimir heat weight times itself. -/
theorem heatKernel_character_eigen {t : ℝ} (ht : 0 < t) (m : ℕ) (g : SU2) :
    Lean2dYangMills.su2Convolution
        (Lean2dYangMills.su2HeatKernel t)
        (Lean2dYangMills.su2CharacterChebyshev m) g =
      Lean2dYangMills.su2ClassHeatWeight t m *
        Lean2dYangMills.su2CharacterChebyshev m g := by
  let M : ℝ := ∑' n, Lean2dYangMills.su2HeatKernelMajorant t n
  let F : ℕ → SU2 → ℂ := fun N x =>
    Lean2dYangMills.su2HeatKernelPartial N t x *
      Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g)
  let f : SU2 → ℂ := fun x =>
    Lean2dYangMills.su2HeatKernel t x *
      Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g)
  have hmeas (N : ℕ) : AEStronglyMeasurable (F N)
      Lean2dYangMills.su2HaarProb := by
    exact
      ((Lean2dYangMills.continuous_su2HeatKernelPartial N t).mul
        ((Lean2dYangMills.continuous_su2CharacterChebyshev m).comp <| by
          fun_prop)).aestronglyMeasurable
  have hM : 0 ≤ M := tsum_nonneg fun _ => by
    unfold Lean2dYangMills.su2HeatKernelMajorant
    positivity
  have hbound (N : ℕ) : ∀ᵐ x : SU2 ∂Lean2dYangMills.su2HaarProb,
      ‖F N x‖ ≤ M * ((m : ℝ) + 1) := by
    exact ae_of_all _ fun x => by
      dsimp [F]
      rw [norm_mul]
      exact mul_le_mul
        (Lean2dYangMills.norm_su2HeatKernelPartial_le_tsum_majorant ht N x)
        (Lean2dYangMills.abs_su2CharacterChebyshev_le m (x⁻¹ * g))
        (norm_nonneg _) hM
  have hlim : ∀ᵐ x : SU2 ∂Lean2dYangMills.su2HaarProb,
      Filter.Tendsto (fun N => F N x) Filter.atTop (nhds (f x)) := by
    exact ae_of_all _ fun x =>
      (Lean2dYangMills.tendsto_su2HeatKernelPartial ht x).mul
        tendsto_const_nhds
  have hleft := tendsto_integral_of_dominated_convergence
    (fun _x : SU2 => M * ((m : ℝ) + 1)) hmeas
      (integrable_const (M * ((m : ℝ) + 1))) hbound hlim
  have hevent : ∀ᶠ N : ℕ in Filter.atTop,
      (∫ x : SU2, F N x ∂Lean2dYangMills.su2HaarProb) =
        Lean2dYangMills.su2ClassHeatWeight t m *
          Lean2dYangMills.su2CharacterChebyshev m g := by
    filter_upwards [Filter.eventually_ge_atTop (m + 1)] with N hN
    exact heatKernelPartial_character_eigen_of_lt N t m
      (lt_of_lt_of_le (Nat.lt_succ_self m) hN) g
  have hright : Filter.Tendsto
      (fun N : ℕ => ∫ x : SU2, F N x ∂Lean2dYangMills.su2HaarProb)
      Filter.atTop
      (nhds (Lean2dYangMills.su2ClassHeatWeight t m *
        Lean2dYangMills.su2CharacterChebyshev m g)) := by
    exact tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)
  change (∫ x : SU2, f x ∂Lean2dYangMills.su2HaarProb) = _
  exact tendsto_nhds_unique hleft hright

/-! ## 2. Exact Casimir rate and sharp fundamental mode -/

/-- The real heat rate attached to the SU(2) highest-weight label `n`. -/
def modeRate (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t * ((n : ℝ) * ((n : ℝ) + 2)) / 4)

theorem classHeatWeight_eq_modeRate (t : ℝ) (n : ℕ) :
    Lean2dYangMills.su2ClassHeatWeight t n = (modeRate t n : ℂ) := by
  unfold Lean2dYangMills.su2ClassHeatWeight modeRate
  norm_cast
  congr 1
  ring

@[simp] theorem modeRate_zero (t : ℝ) : modeRate t 0 = 1 := by
  simp [modeRate]

@[simp] theorem modeRate_one (t : ℝ) :
    modeRate t 1 = Real.exp (-(3 * t / 4)) := by
  unfold modeRate
  congr 1
  ring

theorem modeRate_pos (t : ℝ) (n : ℕ) : 0 < modeRate t n :=
  Real.exp_pos _

theorem casimir_three_le {n : ℕ} (hn : 1 ≤ n) :
    (3 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- The fundamental representation is the slowest non-vacuum heat mode. -/
theorem modeRate_le_fundamental {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (hn : 1 ≤ n) :
    modeRate t n ≤ modeRate t 1 := by
  apply Real.exp_le_exp.mpr
  dsimp [modeRate]
  have hc := casimir_three_le hn
  nlinarith

theorem fundamental_rate_lt_one {t : ℝ} (ht : 0 < t) : modeRate t 1 < 1 := by
  rw [modeRate_one]
  apply Real.exp_lt_one_iff.mpr
  linarith

@[simp] theorem fundamental_character_at_one :
    Lean2dYangMills.su2CharacterChebyshev 1 (1 : SU2) = 2 := by
  rw [Lean2dYangMills.su2CharacterChebyshev_one]
  norm_num

theorem fundamental_character_ne_zero :
    Lean2dYangMills.su2CharacterChebyshev 1 ≠ 0 := by
  intro hzero
  have h := congrFun hzero (1 : SU2)
  norm_num at h

/-- Fundamental specialization of the genuine Haar-integral eigenfunction
identity, with the `3/4` Casimir value exposed in the conclusion. -/
theorem heatKernel_fundamental_eigen {t : ℝ} (ht : 0 < t) (g : SU2) :
    Lean2dYangMills.su2Convolution
        (Lean2dYangMills.su2HeatKernel t)
        (Lean2dYangMills.su2CharacterChebyshev 1) g =
      (Real.exp (-(3 * t / 4)) : ℂ) *
        Lean2dYangMills.su2CharacterChebyshev 1 g := by
  rw [heatKernel_character_eigen ht]
  rw [classHeatWeight_eq_modeRate, modeRate_one]

/-! ## 3. Identification with the finite transport witness -/

/-- The rate used by the finite SU(2)-inhabited Dobrushin witness is exactly
the fundamental eigenvalue of the genuine continuous Haar heat operator. -/
theorem witness_heatRate_eq_fundamental (t : ℝ) :
    Dobrushin.SU2Transport.heatRate t = modeRate t 1 := by
  rw [modeRate_one]
  rfl

/-- End-to-end bridge: the concrete heat kernel has a nonzero fundamental
eigenmode at the exact rate consumed by the already-proved Dobrushin transport
witness, whose projected operator is itself nonzero. -/
theorem continuous_mode_to_finite_transport {t : ℝ} (ht : 0 < t) :
    (∀ g : SU2,
      Lean2dYangMills.su2Convolution
          (Lean2dYangMills.su2HeatKernel t)
          (Lean2dYangMills.su2CharacterChebyshev 1) g =
        (Dobrushin.SU2Transport.heatRate t : ℂ) *
          Lean2dYangMills.su2CharacterChebyshev 1 g) ∧
    Lean2dYangMills.su2CharacterChebyshev 1 ≠ 0 ∧
    (∃ m : ℝ, 0 < m ∧
      ‖projectedTransfer
          (Dobrushin.opOf
            (Dobrushin.SU2Transport.kernel
              (Dobrushin.SU2Transport.heatRate t)))
          (Dobrushin.vacOf
            (fun _ : Dobrushin.SU2Transport.Carrier => (1 : ℝ)))‖ ≤
        Real.exp (-m)) ∧
    projectedTransfer
        (Dobrushin.opOf
          (Dobrushin.SU2Transport.kernel
            (Dobrushin.SU2Transport.heatRate t)))
        (Dobrushin.vacOf
          (fun _ : Dobrushin.SU2Transport.Carrier => (1 : ℝ))) ≠ 0 := by
  refine ⟨fun g => ?_, fundamental_character_ne_zero, ?_⟩
  · rw [heatKernel_fundamental_eigen ht, witness_heatRate_eq_fundamental,
      modeRate_one]
  · exact Dobrushin.SU2Transport.exact_transport_witness ht

end YangMills.OS.SU2HeatTransport

end
