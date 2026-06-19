/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.MeasureTheory.Group.Integral
import YangMills.ClayCore.ContinuousUnitaryRep

/-!
# Haar averaging and generic Schur orthogonality

This file supplies the analytic averaging operator used in the standard proof
of Schur orthogonality. It does not assert Peter-Weyl completeness.
-/

noncomputable section

open Matrix MeasureTheory

namespace YangMills.ClayCore
namespace ContinuousUnitaryMatrixRep

variable {G ι κ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Haar averaging of a matrix under two unitary representations, defined
entrywise to avoid choosing a norm on rectangular matrices. -/
def haarAverageMatrix (μ : Measure G)
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    (A : Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  fun i k => ∫ g,
    ((ρ g : Matrix ι ι ℂ) * A * (σ g : Matrix κ κ ℂ)ᴴ) i k ∂μ

@[simp]
theorem haarAverageMatrix_single_apply
    (μ : Measure G)
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    (i j : ι) (k l : κ) :
    haarAverageMatrix μ ρ σ (Matrix.single j l 1) i k =
      ∫ g, (ρ g : Matrix ι ι ℂ) i j *
        star ((σ g : Matrix κ κ ℂ) k l) ∂μ := by
  apply integral_congr_ae
  filter_upwards with g
  symm
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · simp [conjTranspose_apply]
  · intro b _ hbl
    rw [Matrix.mul_single_apply_of_ne 1 j l i b hbl
      (ρ g : Matrix ι ι ℂ)]
    simp
  · exact fun hnot => absurd (Finset.mem_univ l) hnot

theorem continuous_haarAverageMatrix_entry
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    (A : Matrix ι κ ℂ) (i : ι) (k : κ) :
    Continuous (fun g =>
      ((ρ g : Matrix ι ι ℂ) * A * (σ g : Matrix κ κ ℂ)ᴴ) i k) := by
  have hρ : Continuous (fun g => (ρ g : Matrix ι ι ℂ)) :=
    continuous_subtype_val.comp ρ.continuous_toFun
  have hσ : Continuous (fun g => (σ g : Matrix κ κ ℂ)) :=
    continuous_subtype_val.comp σ.continuous_toFun
  exact ((hρ.matrix_mul continuous_const).matrix_mul
    hσ.matrix_conjTranspose).matrix_elem i k

theorem integrable_haarAverageMatrix_entry
    (μ : Measure G) [IsFiniteMeasure μ]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    (A : Matrix ι κ ℂ) (i : ι) (k : κ) :
    Integrable (fun g =>
      ((ρ g : Matrix ι ι ℂ) * A * (σ g : Matrix κ κ ℂ)ᴴ) i k) μ :=
  (continuous_haarAverageMatrix_entry ρ σ A i k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Haar averaging intertwines the two representations. -/
theorem haarAverageMatrix_mul_eq_mul_haarAverageMatrix
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    (A : Matrix ι κ ℂ) (h : G) :
    haarAverageMatrix μ ρ σ A * (σ h : Matrix κ κ ℂ) =
      (ρ h : Matrix ι ι ℂ) * haarAverageMatrix μ ρ σ A := by
  ext i k
  let F : G → Matrix ι κ ℂ := fun g =>
    (ρ g : Matrix ι ι ℂ) * A * (σ g : Matrix κ κ ℂ)ᴴ
  have hF : ∀ a b, Integrable (fun g => F g a b) μ :=
    fun a b => integrable_haarAverageMatrix_entry μ ρ σ A a b
  have hleft :
      (haarAverageMatrix μ ρ σ A * (σ h : Matrix κ κ ℂ)) i k =
        ∫ g, (F g * (σ h : Matrix κ κ ℂ)) i k ∂μ := by
    rw [Matrix.mul_apply]
    simp only [haarAverageMatrix]
    calc
      (∑ b, (∫ g, F g i b ∂μ) * (σ h : Matrix κ κ ℂ) b k) =
          ∑ b, ∫ g, F g i b * (σ h : Matrix κ κ ℂ) b k ∂μ := by
            apply Finset.sum_congr rfl
            intro b _
            exact (integral_mul_const _ _).symm
      _ = ∫ g, ∑ b, F g i b * (σ h : Matrix κ κ ℂ) b k ∂μ := by
            rw [integral_finset_sum]
            intro b _
            exact (hF i b).mul_const _
      _ = ∫ g, (F g * (σ h : Matrix κ κ ℂ)) i k ∂μ := by
            congr 1
  have hright :
      ((ρ h : Matrix ι ι ℂ) * haarAverageMatrix μ ρ σ A) i k =
        ∫ g, ((ρ h : Matrix ι ι ℂ) * F g) i k ∂μ := by
    rw [Matrix.mul_apply]
    simp only [haarAverageMatrix]
    calc
      (∑ a, (ρ h : Matrix ι ι ℂ) i a * ∫ g, F g a k ∂μ) =
          ∑ a, ∫ g, (ρ h : Matrix ι ι ℂ) i a * F g a k ∂μ := by
            apply Finset.sum_congr rfl
            intro a _
            exact (integral_const_mul _ _).symm
      _ = ∫ g, ∑ a, (ρ h : Matrix ι ι ℂ) i a * F g a k ∂μ := by
            rw [integral_finset_sum]
            intro a _
            exact (hF a k).const_mul _
      _ = ∫ g, ((ρ h : Matrix ι ι ℂ) * F g) i k ∂μ := by
            congr 1
  rw [hleft, hright]
  have hinv := integral_mul_left_eq_self
    (μ := μ) (fun g => (F g * (σ h : Matrix κ κ ℂ)) i k) h
  rw [← hinv]
  congr 1
  funext g
  simp only [F, map_mul, Matrix.UnitaryGroup.mul_val, conjTranspose_mul]
  have hu :
      (σ h : Matrix κ κ ℂ)ᴴ * (σ h : Matrix κ κ ℂ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self (σ h)
  apply congrArg (fun M : Matrix ι κ ℂ => M i k)
  calc
    (ρ h : Matrix ι ι ℂ) * (ρ g : Matrix ι ι ℂ) * A *
          ((σ g : Matrix κ κ ℂ)ᴴ * (σ h : Matrix κ κ ℂ)ᴴ) *
          (σ h : Matrix κ κ ℂ) =
        ((ρ h : Matrix ι ι ℂ) * (ρ g : Matrix ι ι ℂ) * A) *
          (((σ g : Matrix κ κ ℂ)ᴴ * (σ h : Matrix κ κ ℂ)ᴴ) *
            (σ h : Matrix κ κ ℂ)) := by simp only [Matrix.mul_assoc]
    _ = ((ρ h : Matrix ι ι ℂ) * (ρ g : Matrix ι ι ℂ) * A) *
          ((σ g : Matrix κ κ ℂ)ᴴ *
            ((σ h : Matrix κ κ ℂ)ᴴ * (σ h : Matrix κ κ ℂ))) := by
          simp only [Matrix.mul_assoc]
    _ = (ρ h : Matrix ι ι ℂ) *
          ((ρ g : Matrix ι ι ℂ) * A * (σ g : Matrix κ κ ℂ)ᴴ) := by
          rw [hu]
          simp only [Matrix.mul_assoc, Matrix.mul_one]

/-- The Haar-averaged matrix as an intertwiner from `σ` to `ρ`. -/
def haarAverageIntertwiner
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    (A : Matrix ι κ ℂ) :
    σ.IntertwiningMap ρ where
  toLinearMap := Matrix.toLin' (haarAverageMatrix μ ρ σ A)
  isIntertwining' h := by
    change (Matrix.toLin' (haarAverageMatrix μ ρ σ A)).comp
        (Matrix.toLin' (σ h : Matrix κ κ ℂ)) =
      (Matrix.toLin' (ρ h : Matrix ι ι ℂ)).comp
        (Matrix.toLin' (haarAverageMatrix μ ρ σ A))
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      haarAverageMatrix_mul_eq_mul_haarAverageMatrix]

@[simp]
theorem haarAverageIntertwiner_apply
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    (A : Matrix ι κ ℂ) (v : κ → ℂ) :
    haarAverageIntertwiner μ ρ σ A v =
      haarAverageMatrix μ ρ σ A *ᵥ v :=
  rfl

/-- Haar averaging between inequivalent irreducible representations vanishes. -/
theorem haarAverageMatrix_eq_zero_of_not_equiv
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    [IsEmpty (Representation.Equiv σ.toRepresentation ρ.toRepresentation)]
    (A : Matrix ι κ ℂ) :
    haarAverageMatrix μ ρ σ A = 0 := by
  have hinter :
      haarAverageIntertwiner μ ρ σ A = 0 :=
    Subsingleton.elim _ _
  have hlin :
      Matrix.toLin' (haarAverageMatrix μ ρ σ A) = 0 :=
    congrArg Representation.IntertwiningMap.toLinearMap hinter
  calc
    haarAverageMatrix μ ρ σ A =
        LinearMap.toMatrix' (Matrix.toLin' (haarAverageMatrix μ ρ σ A)) :=
      (LinearMap.toMatrix'_toLin' _).symm
    _ = LinearMap.toMatrix' (0 : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)) := by rw [hlin]
    _ = 0 := by
      ext i k
      simp [LinearMap.toMatrix'_apply]

/-- Haar averaging within one irreducible representation is a scalar matrix. -/
theorem exists_haarAverageMatrix_eq_smul_one
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι) [ρ.IsIrreducible]
    (A : Matrix ι ι ℂ) :
    ∃ c : ℂ, haarAverageMatrix μ ρ ρ A = c • 1 := by
  rcases exists_eq_smul_one_of_self_intertwiner ρ
      (haarAverageIntertwiner μ ρ ρ A) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hlin := congrArg Representation.IntertwiningMap.toLinearMap hc
  have hone :
      (1 : ρ.IntertwiningMap ρ).toLinearMap = LinearMap.id := by
    ext v
    rfl
  have hlin' :
      Matrix.toLin' (haarAverageMatrix μ ρ ρ A) =
        c • (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) := by
    change Matrix.toLin' (haarAverageMatrix μ ρ ρ A) =
      (c • (1 : ρ.IntertwiningMap ρ)).toLinearMap at hlin
    simpa [Representation.IntertwiningMap.toLinearMap_smul, hone] using hlin
  calc
    haarAverageMatrix μ ρ ρ A =
        LinearMap.toMatrix' (Matrix.toLin' (haarAverageMatrix μ ρ ρ A)) :=
      (LinearMap.toMatrix'_toLin' _).symm
    _ = LinearMap.toMatrix'
        (c • (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))) := by rw [hlin']
    _ = c • 1 := by
      ext i k
      simp [LinearMap.toMatrix'_apply, Matrix.one_apply, Pi.single_apply]

/-- Probability-Haar averaging preserves matrix trace. -/
theorem trace_haarAverageMatrix
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (A : Matrix ι ι ℂ) :
    trace (haarAverageMatrix μ ρ ρ A) = trace A := by
  rw [trace]
  change (∑ i, ∫ g, ((ρ g : Matrix ι ι ℂ) * A *
    (ρ g : Matrix ι ι ℂ)ᴴ) i i ∂μ) = trace A
  rw [← integral_finset_sum]
  · calc
      (∫ g, ∑ i, ((ρ g : Matrix ι ι ℂ) * A *
          (ρ g : Matrix ι ι ℂ)ᴴ) i i ∂μ) =
          ∫ g, trace ((ρ g : Matrix ι ι ℂ) * A *
            (ρ g : Matrix ι ι ℂ)ᴴ) ∂μ := by
            congr 1
      _ = ∫ _g : G, trace A ∂μ := by
            apply integral_congr_ae
            filter_upwards with g
            simpa using
              (Matrix.trace_units_conj (Unitary.toUnits (ρ g)) A)
      _ = trace A := by
        rw [integral_const]
        simp [measureReal_def]
        exact one_smul ℝ (trace A)
  · intro i _
    exact integrable_haarAverageMatrix_entry μ ρ ρ A i i

/-- The exact scalar in the self-representation Haar average. -/
theorem haarAverageMatrix_eq_trace_div_card_smul_one
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι) [ρ.IsIrreducible]
    [Nonempty ι] (A : Matrix ι ι ℂ) :
    haarAverageMatrix μ ρ ρ A =
      (trace A / (Fintype.card ι : ℂ)) • 1 := by
  rcases exists_haarAverageMatrix_eq_smul_one μ ρ A with ⟨c, hc⟩
  have htrace := congrArg trace hc
  rw [trace_haarAverageMatrix] at htrace
  have hcard : (Fintype.card ι : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcval : c = trace A / (Fintype.card ι : ℂ) := by
    have hmul : trace A = c * (Fintype.card ι : ℂ) := by
      simpa [trace, Matrix.one_apply, mul_comm] using htrace
    apply (eq_div_iff hcard).2
    exact hmul.symm
  rw [hc, hcval]

/-- Matrix coefficients of inequivalent irreducible unitary representations
are orthogonal in Haar `L²`. -/
theorem integral_matrixCoeff_mul_star_eq_zero_of_not_equiv
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    [IsEmpty (Representation.Equiv σ.toRepresentation ρ.toRepresentation)]
    (i j : ι) (k l : κ) :
    (∫ g, (ρ g : Matrix ι ι ℂ) i j *
      star ((σ g : Matrix κ κ ℂ) k l) ∂μ) = 0 := by
  have h := congrArg (fun M : Matrix ι κ ℂ => M i k)
    (haarAverageMatrix_eq_zero_of_not_equiv μ ρ σ (Matrix.single j l 1))
  simpa using h

/-- **Generic Schur orthogonality within one irreducible representation.** -/
theorem integral_matrixCoeff_mul_star
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι) [ρ.IsIrreducible]
    [Nonempty ι] (i j k l : ι) :
    (∫ g, (ρ g : Matrix ι ι ℂ) i j *
      star ((ρ g : Matrix ι ι ℂ) k l) ∂μ) =
      if i = k ∧ j = l then (1 : ℂ) / (Fintype.card ι : ℂ) else 0 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M i k)
    (haarAverageMatrix_eq_trace_div_card_smul_one μ ρ (Matrix.single j l 1))
  have hsingle :
      trace (Matrix.single j l (1 : ℂ)) = if j = l then 1 else 0 := by
    by_cases hjl : j = l
    · subst l
      simp [trace]
    · simp [trace, hjl]
  rw [hsingle] at h
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simpa [Matrix.one_apply] using h
    · simpa [Matrix.one_apply, hjl] using h
  · simpa [Matrix.one_apply, hik] using h

/-- Characters of inequivalent irreducible unitary representations are
orthogonal in Haar `L²`. -/
theorem integral_character_mul_star_eq_zero_of_not_equiv
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    [IsEmpty (Representation.Equiv σ.toRepresentation ρ.toRepresentation)] :
    (∫ g, ρ.character g * star (σ.character g) ∂μ) = 0 := by
  have hsplit :
      (fun g : G => ρ.character g * star (σ.character g)) =
        fun g => ∑ i, ∑ k,
          (ρ g : Matrix ι ι ℂ) i i *
            star ((σ g : Matrix κ κ ℂ) k k) := by
    funext g
    simp [character_apply, trace, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsplit]
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro k _
      exact integral_matrixCoeff_mul_star_eq_zero_of_not_equiv μ ρ σ i i k k
    · intro k _
      have hcont : Continuous (fun a : G =>
          (ρ a : Matrix ι ι ℂ) i i *
            star ((σ a : Matrix κ κ ℂ) k k)) := by
        exact ((continuous_subtype_val.comp ρ.continuous_toFun).matrix_elem i i).mul
          (((continuous_subtype_val.comp σ.continuous_toFun).matrix_elem k k).star)
      exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro i _
    have hcont : Continuous (fun g : G => ∑ k,
        (ρ g : Matrix ι ι ℂ) i i *
          star ((σ g : Matrix κ κ ℂ) k k)) := by
      refine continuous_finset_sum _ (fun k _ => ?_)
      exact ((continuous_subtype_val.comp ρ.continuous_toFun).matrix_elem i i).mul
        (((continuous_subtype_val.comp σ.continuous_toFun).matrix_elem k k).star)
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- An irreducible unitary character has Haar `L²` norm one. -/
theorem integral_character_mul_star
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι) [ρ.IsIrreducible] [Nonempty ι] :
    (∫ g, ρ.character g * star (ρ.character g) ∂μ) = 1 := by
  classical
  have hsplit :
      (fun g : G => ρ.character g * star (ρ.character g)) =
        fun g => ∑ i, ∑ k,
          (ρ g : Matrix ι ι ℂ) i i *
            star ((ρ g : Matrix ι ι ℂ) k k) := by
    funext g
    simp [character_apply, trace, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsplit]
  rw [integral_finset_sum]
  · calc
      (∑ i, ∫ g, ∑ k, (ρ g : Matrix ι ι ℂ) i i *
          star ((ρ g : Matrix ι ι ℂ) k k) ∂μ)
          = ∑ i, ∑ k, ∫ g, (ρ g : Matrix ι ι ℂ) i i *
              star ((ρ g : Matrix ι ι ℂ) k k) ∂μ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [integral_finset_sum]
            intro k _
            have hcont : Continuous (fun g : G =>
                (ρ g : Matrix ι ι ℂ) i i *
                  star ((ρ g : Matrix ι ι ℂ) k k)) := by
              exact ((continuous_subtype_val.comp ρ.continuous_toFun).matrix_elem i i).mul
                (((continuous_subtype_val.comp ρ.continuous_toFun).matrix_elem k k).star)
            exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      _ = ∑ i : ι, (1 : ℂ) / (Fintype.card ι : ℂ) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_eq_single i]
            · rw [integral_matrixCoeff_mul_star μ ρ i i i i]
              simp
            · intro k _ hki
              rw [integral_matrixCoeff_mul_star μ ρ i i k k]
              simp [Ne.symm hki]
            · intro hnot
              exact absurd (Finset.mem_univ i) hnot
      _ = 1 := by
            have hcard : (Fintype.card ι : ℂ) ≠ 0 :=
              Nat.cast_ne_zero.mpr Fintype.card_ne_zero
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            simp [div_eq_mul_inv, hcard]
  · intro i _
    have hcont : Continuous (fun g : G => ∑ k,
        (ρ g : Matrix ι ι ℂ) i i *
          star ((ρ g : Matrix ι ι ℂ) k k)) := by
      refine continuous_finset_sum _ (fun k _ => ?_)
      exact ((continuous_subtype_val.comp ρ.continuous_toFun).matrix_elem i i).mul
        (((continuous_subtype_val.comp ρ.continuous_toFun).matrix_elem k k).star)
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Characters of inequivalent irreducible unitary representations are
orthogonal as vectors in Haar `L²`. -/
theorem inner_characterL2_eq_zero_of_not_equiv
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    [IsEmpty (Representation.Equiv σ.toRepresentation ρ.toRepresentation)] :
    inner ℂ (σ.characterL2 μ) (ρ.characterL2 μ) = 0 := by
  rw [characterL2, characterL2, ContinuousMap.inner_toLp]
  exact integral_character_mul_star_eq_zero_of_not_equiv μ ρ σ

/-- An irreducible unitary character has unit norm as a vector in Haar `L²`. -/
theorem inner_characterL2
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : ContinuousUnitaryMatrixRep G ι) [ρ.IsIrreducible] [Nonempty ι] :
    inner ℂ (ρ.characterL2 μ) (ρ.characterL2 μ) = 1 := by
  rw [characterL2, ContinuousMap.inner_toLp]
  exact integral_character_mul_star μ ρ

/-- A finite family of pairwise inequivalent irreducible unitary characters is
orthonormal in Haar `L²`. This is still only the finite-family substrate; it
does not assert Peter-Weyl completeness. -/
theorem orthonormal_characterL2
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : α → ContinuousUnitaryMatrixRep G ι)
    [∀ a, (ρ a).IsIrreducible] [Nonempty ι]
    (hineq : ∀ ⦃a b : α⦄, a ≠ b →
      IsEmpty (Representation.Equiv (ρ a).toRepresentation (ρ b).toRepresentation)) :
    Orthonormal ℂ (fun a => (ρ a).characterL2 μ) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  by_cases h : a = b
  · subst b
    simpa using inner_characterL2 μ (ρ a)
  · haveI : IsEmpty
        (Representation.Equiv (ρ a).toRepresentation (ρ b).toRepresentation) :=
      hineq h
    simpa [h] using inner_characterL2_eq_zero_of_not_equiv μ (ρ b) (ρ a)

/-- Finite families of pairwise inequivalent irreducible unitary characters are
linearly independent in Haar `L²`. -/
theorem linearIndependent_characterL2
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : α → ContinuousUnitaryMatrixRep G ι)
    [∀ a, (ρ a).IsIrreducible] [Nonempty ι]
    (hineq : ∀ ⦃a b : α⦄, a ≠ b →
      IsEmpty (Representation.Equiv (ρ a).toRepresentation (ρ b).toRepresentation)) :
    LinearIndependent ℂ (fun a => (ρ a).characterL2 μ) :=
  (orthonormal_characterL2 μ ρ hineq).linearIndependent

/-- Finite character expansion coefficients are recovered by Haar `L²` inner
product against the corresponding irreducible character. -/
theorem inner_characterL2_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : α → ContinuousUnitaryMatrixRep G ι)
    [∀ a, (ρ a).IsIrreducible] [Nonempty ι]
    (hineq : ∀ ⦃a b : α⦄, a ≠ b →
      IsEmpty (Representation.Equiv (ρ a).toRepresentation (ρ b).toRepresentation))
    (c : α → ℂ) (a : α) :
    inner ℂ ((ρ a).characterL2 μ)
      (∑ b, c b • (ρ b).characterL2 μ) = c a := by
  classical
  simpa using
    (orthonormal_characterL2 μ ρ hineq).inner_right_sum c
      (s := Finset.univ) (i := a) (Finset.mem_univ a)

/-- Finite character expansions in a fixed pairwise-inequivalent irreducible
family have unique coefficients.  This is still a finite-family statement, not
Peter-Weyl completeness. -/
theorem characterL2_sum_eq_sum_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : α → ContinuousUnitaryMatrixRep G ι)
    [∀ a, (ρ a).IsIrreducible] [Nonempty ι]
    (hineq : ∀ ⦃a b : α⦄, a ≠ b →
      IsEmpty (Representation.Equiv (ρ a).toRepresentation (ρ b).toRepresentation))
    (c d : α → ℂ) :
    (∑ a, c a • (ρ a).characterL2 μ =
      ∑ a, d a • (ρ a).characterL2 μ) ↔ c = d := by
  classical
  constructor
  · intro h
    funext a
    have hinner := congrArg
      (fun v => inner ℂ ((ρ a).characterL2 μ) v) h
    simpa [inner_characterL2_sum μ ρ hineq c a,
      inner_characterL2_sum μ ρ hineq d a] using hinner
  · intro h
    subst h
    rfl

/-- A finite character expansion in a fixed pairwise-inequivalent irreducible
family vanishes iff all its coefficients vanish. -/
theorem characterL2_sum_eq_zero_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : α → ContinuousUnitaryMatrixRep G ι)
    [∀ a, (ρ a).IsIrreducible] [Nonempty ι]
    (hineq : ∀ ⦃a b : α⦄, a ≠ b →
      IsEmpty (Representation.Equiv (ρ a).toRepresentation (ρ b).toRepresentation))
    (c : α → ℂ) :
    (∑ a, c a • (ρ a).characterL2 μ = 0) ↔ c = 0 := by
  classical
  have hzero :
      (∑ a, (0 : α → ℂ) a • (ρ a).characterL2 μ) = 0 := by
    simp
  constructor
  · intro h
    exact (characterL2_sum_eq_sum_iff μ ρ hineq c 0).1 (by simpa [hzero] using h)
  · intro h
    subst h
    simp

/-- Finite character expansions in a fixed pairwise-inequivalent irreducible
family have the expected diagonal Haar `L²` inner product. -/
theorem inner_characterL2_sum_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : α → ContinuousUnitaryMatrixRep G ι)
    [∀ a, (ρ a).IsIrreducible] [Nonempty ι]
    (hineq : ∀ ⦃a b : α⦄, a ≠ b →
      IsEmpty (Representation.Equiv (ρ a).toRepresentation (ρ b).toRepresentation))
    (c d : α → ℂ) :
    inner ℂ (∑ a, c a • (ρ a).characterL2 μ)
      (∑ a, d a • (ρ a).characterL2 μ) =
        ∑ a, star (c a) * d a := by
  classical
  simpa using
    (orthonormal_characterL2 μ ρ hineq).inner_sum c d Finset.univ

end ContinuousUnitaryMatrixRep
end YangMills.ClayCore
