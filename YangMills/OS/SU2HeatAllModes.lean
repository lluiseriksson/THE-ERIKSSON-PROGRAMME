/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.SU2HeatIntertwining

/-!
# Exact algebraic all-mode intertwining for SU(2) heat transport

The preceding bridge packages the vacuum and fundamental characters into a
two-dimensional common coefficient space.  This module removes that fixed
cutoff.  Its coefficient object is the algebraic direct sum `ℕ →₀ ℝ`; hence
one theorem simultaneously covers every finite real character expansion.

The lift lands in genuine functions on bundled `SU(2)`.  Haar orthogonality
recovers every coefficient, proves injectivity and gives the exact pairing.
For positive heat time, convolution by the actual infinite SU(2) heat kernel
intertwines the lift with the exact diagonal Casimir step.

Scope: the algebraic direct sum contains all finite character expansions.  No
Peter--Weyl completeness statement and no diagonalization of completed
`L²(SU(2))` is asserted here.
-/

noncomputable section

namespace YangMills.OS.SU2HeatAllModes

open Finset MeasureTheory
open scoped BigOperators

abbrev SU2 := Lean2dYangMills.SU2

/-- The single, unbounded algebraic coefficient model for all SU(2) character
modes.  Every inhabitant has finite support, but there is no fixed cutoff. -/
abbrev AlgebraicModes := ℕ →₀ ℝ

/-- Lift a finite-support real coefficient sequence to an actual complex
class function on bundled `SU(2)`. -/
def characterLift (a : AlgebraicModes) (g : SU2) : ℂ :=
  a.sum fun n c => (c : ℂ) * Lean2dYangMills.su2CharacterChebyshev n g

/-- The exact diagonal Casimir heat step on the algebraic direct sum. -/
def spectralStep (t : ℝ) (a : AlgebraicModes) : AlgebraicModes :=
  a.sum fun n c =>
    Finsupp.single n (SU2HeatTransport.modeRate t n * c)

/-- Actual normalized-Haar convolution by the infinite SU(2) heat kernel. -/
def heatOperator (t : ℝ) (f : SU2 → ℂ) (g : SU2) : ℂ :=
  Lean2dYangMills.su2Convolution (Lean2dYangMills.su2HeatKernel t) f g

@[simp] theorem characterLift_single (n : ℕ) (c : ℝ) (g : SU2) :
    characterLift (Finsupp.single n c) g =
      (c : ℂ) * Lean2dYangMills.su2CharacterChebyshev n g := by
  simp [characterLift]

@[simp] theorem spectralStep_apply (t : ℝ) (a : AlgebraicModes) (n : ℕ) :
    spectralStep t a n = SU2HeatTransport.modeRate t n * a n := by
  classical
  rw [spectralStep, Finsupp.sum_apply]
  change (∑ k ∈ a.support, Finsupp.single k
    (SU2HeatTransport.modeRate t k * a k) n) =
      SU2HeatTransport.modeRate t n * a n
  by_cases hn : n ∈ a.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro k hk hkn
      rw [Finsupp.single_eq_of_ne (Ne.symm hkn)]
    · exact fun h => (h hn).elim
  · have han : a n = 0 := by simpa using hn
    rw [han, mul_zero]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k ≠ n := by
      intro h
      subst k
      exact hn hk
    rw [Finsupp.single_eq_of_ne (Ne.symm hkn)]

@[simp] theorem spectralStep_single (t : ℝ) (n : ℕ) (c : ℝ) :
    spectralStep t (Finsupp.single n c) =
      Finsupp.single n (SU2HeatTransport.modeRate t n * c) := by
  ext m
  simp [spectralStep_apply]
  by_cases h : m = n
  · subst m
    simp
  · simp [h]

theorem continuous_characterLift (a : AlgebraicModes) :
    Continuous (characterLift a) := by
  classical
  change Continuous (fun g : SU2 => ∑ n ∈ a.support,
    (a n : ℂ) * Lean2dYangMills.su2CharacterChebyshev n g)
  refine continuous_finset_sum a.support fun n hn => ?_
  exact continuous_const.mul
    (Lean2dYangMills.continuous_su2CharacterChebyshev n)

theorem integrable_characterLift_mul_character (a : AlgebraicModes) (m : ℕ) :
    Integrable
      (fun g : SU2 => characterLift a g *
        Lean2dYangMills.su2CharacterChebyshev m g)
      Lean2dYangMills.su2HaarProb := by
  apply Lean2dYangMills.integrable_continuous_su2Haar
  exact (continuous_characterLift a).mul
    (Lean2dYangMills.continuous_su2CharacterChebyshev m)

/-- Haar pairing against one character recovers the corresponding coefficient
exactly.  This is the decisive non-vacuity theorem for the algebraic lift. -/
theorem coefficient_extraction (a : AlgebraicModes) (m : ℕ) :
    (∫ g : SU2, characterLift a g *
        Lean2dYangMills.su2CharacterChebyshev m g
      ∂Lean2dYangMills.su2HaarProb) = (a m : ℂ) := by
  classical
  rw [show (fun g : SU2 => characterLift a g *
        Lean2dYangMills.su2CharacterChebyshev m g) =
      fun g => ∑ n ∈ a.support,
        (a n : ℂ) *
          (Lean2dYangMills.su2CharacterChebyshev n g *
            Lean2dYangMills.su2CharacterChebyshev m g) by
      funext g
      simp only [characterLift, Finsupp.sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      ring]
  rw [MeasureTheory.integral_finset_sum a.support]
  · have hterm (n : ℕ) :
        (∫ g : SU2, (a n : ℂ) *
            (Lean2dYangMills.su2CharacterChebyshev n g *
              Lean2dYangMills.su2CharacterChebyshev m g)
          ∂Lean2dYangMills.su2HaarProb) =
          (a n : ℂ) * (if n = m then 1 else 0) := by
        calc
          (∫ g : SU2, (a n : ℂ) *
              (Lean2dYangMills.su2CharacterChebyshev n g *
                Lean2dYangMills.su2CharacterChebyshev m g)
            ∂Lean2dYangMills.su2HaarProb) =
              (a n : ℂ) *
                (∫ g : SU2,
                  Lean2dYangMills.su2CharacterChebyshev n g *
                    Lean2dYangMills.su2CharacterChebyshev m g
                  ∂Lean2dYangMills.su2HaarProb) :=
            MeasureTheory.integral_const_mul _ _
          _ = (a n : ℂ) * (if n = m then 1 else 0) := by
            rw [Lean2dYangMills.integral_su2CharacterChebyshev_mul]
    simp_rw [hterm]
    by_cases hm : m ∈ a.support
    · rw [Finset.sum_eq_single m]
      · simp
      · intro n hn hne
        simp [hne]
      · exact fun h => (h hm).elim
    · have ham : a m = 0 := by simpa using hm
      rw [ham]
      simp only [Complex.ofReal_zero]
      apply Finset.sum_eq_zero
      intro n hn
      have hne : n ≠ m := by
        intro h
        subst n
        exact hm hn
      simp [hne]
  · intro n hn
    apply (Lean2dYangMills.integrable_continuous_su2Haar
      ((Lean2dYangMills.continuous_su2CharacterChebyshev n).mul
        (Lean2dYangMills.continuous_su2CharacterChebyshev m))).const_mul

/-- The algebraic character lift is genuinely injective; no linear
independence hypothesis is loaded into the theorem. -/
theorem characterLift_injective : Function.Injective characterLift := by
  intro a b hab
  ext m
  have hfun : (fun g : SU2 => characterLift a g *
      Lean2dYangMills.su2CharacterChebyshev m g) =
    fun g => characterLift b g *
      Lean2dYangMills.su2CharacterChebyshev m g := by
    funext g
    rw [hab]
  have hint :
      (∫ g : SU2, characterLift a g *
          Lean2dYangMills.su2CharacterChebyshev m g
        ∂Lean2dYangMills.su2HaarProb) =
      (∫ g : SU2, characterLift b g *
          Lean2dYangMills.su2CharacterChebyshev m g
        ∂Lean2dYangMills.su2HaarProb) := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun g => congrFun hfun g
  rw [coefficient_extraction a m, coefficient_extraction b m] at hint
  exact Complex.ofReal_injective hint

/-- Exact Haar pairing for arbitrary finite-support coefficient sequences. -/
theorem characterLift_haar_pairing (a b : AlgebraicModes) :
    (∫ g : SU2, characterLift a g * characterLift b g
      ∂Lean2dYangMills.su2HaarProb) =
      ∑ n ∈ b.support, ((a n * b n : ℝ) : ℂ) := by
  classical
  rw [show (fun g : SU2 => characterLift a g * characterLift b g) =
      fun g => ∑ n ∈ b.support,
        (b n : ℂ) *
          (characterLift a g *
            Lean2dYangMills.su2CharacterChebyshev n g) by
      funext g
      simp only [characterLift, Finsupp.sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring]
  rw [MeasureTheory.integral_finset_sum b.support]
  · have hterm (n : ℕ) :
        (∫ g : SU2, (b n : ℂ) *
            (characterLift a g *
              Lean2dYangMills.su2CharacterChebyshev n g)
          ∂Lean2dYangMills.su2HaarProb) =
          (b n : ℂ) * (a n : ℂ) := by
        calc
          (∫ g : SU2, (b n : ℂ) *
              (characterLift a g *
                Lean2dYangMills.su2CharacterChebyshev n g)
            ∂Lean2dYangMills.su2HaarProb) =
              (b n : ℂ) *
                (∫ g : SU2, characterLift a g *
                  Lean2dYangMills.su2CharacterChebyshev n g
                  ∂Lean2dYangMills.su2HaarProb) :=
            MeasureTheory.integral_const_mul _ _
          _ = (b n : ℂ) * (a n : ℂ) := by
            rw [coefficient_extraction]
    simp_rw [hterm]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  · intro n hn
    exact (integrable_characterLift_mul_character a n).const_mul _

/-- The continuous commuting diagram on the entire algebraic character span:
actual infinite-kernel Haar convolution is conjugate, through the injective
lift, to the diagonal Casimir step. -/
theorem heatOperator_characterLift {t : ℝ} (ht : 0 < t)
    (a : AlgebraicModes) :
    heatOperator t (characterLift a) =
      characterLift (spectralStep t a) := by
  classical
  funext g
  rw [heatOperator, Lean2dYangMills.su2Convolution]
  change (∫ x : SU2, Lean2dYangMills.su2HeatKernel t x *
      characterLift a (x⁻¹ * g) ∂Lean2dYangMills.su2HaarProb) = _
  rw [show (fun x : SU2 => Lean2dYangMills.su2HeatKernel t x *
        characterLift a (x⁻¹ * g)) =
      fun x => ∑ n ∈ a.support, (a n : ℂ) *
        (Lean2dYangMills.su2HeatKernel t x *
          Lean2dYangMills.su2CharacterChebyshev n (x⁻¹ * g)) by
      funext x
      simp only [characterLift, Finsupp.sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring]
  rw [MeasureTheory.integral_finset_sum a.support]
  · have hterm (n : ℕ) :
        (∫ x : SU2, (a n : ℂ) *
            (Lean2dYangMills.su2HeatKernel t x *
              Lean2dYangMills.su2CharacterChebyshev n (x⁻¹ * g))
          ∂Lean2dYangMills.su2HaarProb) =
          (a n : ℂ) * Lean2dYangMills.su2Convolution
            (Lean2dYangMills.su2HeatKernel t)
            (Lean2dYangMills.su2CharacterChebyshev n) g := by
        calc
          (∫ x : SU2, (a n : ℂ) *
              (Lean2dYangMills.su2HeatKernel t x *
                Lean2dYangMills.su2CharacterChebyshev n (x⁻¹ * g))
            ∂Lean2dYangMills.su2HaarProb) =
              (a n : ℂ) *
                (∫ x : SU2, Lean2dYangMills.su2HeatKernel t x *
                  Lean2dYangMills.su2CharacterChebyshev n (x⁻¹ * g)
                  ∂Lean2dYangMills.su2HaarProb) :=
            MeasureTheory.integral_const_mul _ _
          _ = (a n : ℂ) * Lean2dYangMills.su2Convolution
              (Lean2dYangMills.su2HeatKernel t)
              (Lean2dYangMills.su2CharacterChebyshev n) g := rfl
    simp_rw [hterm]
    change (∑ n ∈ a.support, (a n : ℂ) *
      Lean2dYangMills.su2Convolution
        (Lean2dYangMills.su2HeatKernel t)
        (Lean2dYangMills.su2CharacterChebyshev n) g) = _
    simp_rw [SU2HeatTransport.heatKernel_character_eigen ht]
    simp_rw [SU2HeatTransport.classHeatWeight_eq_modeRate]
    rw [show characterLift (spectralStep t a) g =
        ∑ n ∈ a.support,
          ((SU2HeatTransport.modeRate t n * a n : ℝ) : ℂ) *
            Lean2dYangMills.su2CharacterChebyshev n g by
      rw [characterLift, spectralStep, Finsupp.sum_sum_index]
      · calc
          _ = a.sum (fun n b =>
              ((SU2HeatTransport.modeRate t n * b : ℝ) : ℂ) *
                Lean2dYangMills.su2CharacterChebyshev n g) := by
            apply Finsupp.sum_congr
            intro n hn
            rw [Finsupp.sum_single_index]
            simp
          _ = _ := by
            apply Finset.sum_congr rfl
            intro n hn
            push_cast
            ring
      · intro n
        simp
      · intro n x y
        push_cast
        ring]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  · intro n hn
    exact (SU2HeatIntertwining.integrable_heatKernel_mul_character ht n g).const_mul _

/-- Published all-mode endpoint.  It packages exact non-vacuity, Haar
isometry and the actual operator intertwining without any fixed mode cutoff. -/
theorem exact_algebraic_all_mode_intertwining {t : ℝ} (ht : 0 < t) :
    Function.Injective characterLift ∧
    (∀ a b : AlgebraicModes,
      (∫ g : SU2, characterLift a g * characterLift b g
        ∂Lean2dYangMills.su2HaarProb) =
        ∑ n ∈ b.support, ((a n * b n : ℝ) : ℂ)) ∧
    (∀ a : AlgebraicModes,
      heatOperator t (characterLift a) =
        characterLift (spectralStep t a)) := by
  exact ⟨characterLift_injective, characterLift_haar_pairing,
    heatOperator_characterLift ht⟩

end YangMills.OS.SU2HeatAllModes

end
