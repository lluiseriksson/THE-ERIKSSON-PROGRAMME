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

end ContinuousUnitaryMatrixRep
end YangMills.ClayCore
