/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientLocalNearLogThirdJetBound
import YangMills.RG.BalabanCMP102AmbientLogAverageBudget

/-!
# Third jet of the normalized CMP98 logarithmic average

The literal logarithmic average is a normalized finite sum over one
physical block.  This file differentiates that sum locally, then uses the
exact identity `|blockOf| = M^d` to cancel its cardinality.  Thus the third
jet inherits the pointwise local-logarithm budget with no block-volume or
ambient-volume loss.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
  [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102AmbientLogAverageThirdJetMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

local instance cmp102AmbientLogAverageThirdJetCMLSeminormed (n : ℕ) :
    SeminormedAddCommGroup
      (PhysicalAmbientMatrixTangent d (M * N') Nc [×n]→L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousMultilinearMap.seminormedAddCommGroup

local instance cmp102AmbientLogAverageThirdJetCMLNormedSpace (n : ℕ) :
    NormedSpace ℝ
      (PhysicalAmbientMatrixTangent d (M * N') Nc [×n]→L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousMultilinearMap.normedSpace

/-- Local finite-sum differentiation, stated separately because the
summands need only be smooth at the physical point. -/
theorem iteratedFDeriv_finset_sum_apply_of_contDiffAt
    {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Finset ι) (f : ι → E → F) (Z : E) (n : ℕ)
    (hf : ∀ j ∈ s, ContDiffAt ℝ n (f j) Z) :
    iteratedFDeriv ℝ n (fun W => ∑ j ∈ s, f j W) Z =
      ∑ j ∈ s, iteratedFDeriv ℝ n (f j) Z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hfa : ContDiffAt ℝ n (f a) Z :=
        hf a (Finset.mem_insert_self a s)
      have hfs : ∀ j ∈ s, ContDiffAt ℝ n (f j) Z :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hfun :
          (fun W => ∑ j ∈ insert a s, f j W) =
            fun W => f a W + ∑ j ∈ s, f j W := by
        funext W
        rw [Finset.sum_insert ha]
      rw [hfun]
      change iteratedFDeriv ℝ n
        (f a + fun W => ∑ j ∈ s, f j W) Z = _
      rw [iteratedFDeriv_add_apply hfa (ContDiffAt.sum hfs),
        ih hfs, Finset.sum_insert ha]

/-- Exact derivative of the normalized logarithmic average as the
normalized sum of the literal pointwise derivatives. -/
theorem iteratedFDeriv_cmp98UbarLogAverage_eq_normalized_sum
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (n : ℕ)
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1) :
    iteratedFDeriv ℝ n (cmp98UbarLogAverage U b) Z =
      ((M : ℝ) ^ d)⁻¹ •
        ∑ x ∈ blockOf M N' b.1,
          iteratedFDeriv ℝ n
            (fun W =>
              nearLog
                (cmp98UbarAmbientDeviationMatrix U b x W)) Z := by
  let f : FinBox d (M * N') →
      PhysicalAmbientMatrixTangent d (M * N') Nc →
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x W =>
      nearLog (cmp98UbarAmbientDeviationMatrix U b x W)
  have hf : ∀ x ∈ blockOf M N' b.1, ContDiffAt ℝ n (f x) Z := by
    intro x hx
    exact
      (analyticAt_nearLog_of_norm_lt_one (hsmall x hx)).contDiffAt.of_le
        le_top |>.comp Z
          ((analyticAt_cmp98UbarAmbientDeviationMatrix U b x Z
            ).contDiffAt.of_le le_top)
  have hsum :
      iteratedFDeriv ℝ n
          (fun W => ∑ x ∈ blockOf M N' b.1, f x W) Z =
        ∑ x ∈ blockOf M N' b.1,
          iteratedFDeriv ℝ n (f x) Z :=
    iteratedFDeriv_finset_sum_apply_of_contDiffAt
      (blockOf M N' b.1) f Z n hf
  have hsumSmooth :
      ContDiffAt ℝ n
        (fun W => ∑ x ∈ blockOf M N' b.1, f x W) Z :=
    ContDiffAt.sum hf
  have hfun :
      cmp98UbarLogAverage U b =
        fun W => ((M : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf M N' b.1, f x W := by
    funext W
    rfl
  rw [hfun]
  change iteratedFDeriv ℝ n
    (((M : ℝ) ^ d)⁻¹ •
      fun W => ∑ x ∈ blockOf M N' b.1, f x W) Z = _
  calc
    _ = ((M : ℝ) ^ d)⁻¹ •
        iteratedFDeriv ℝ n
          (fun W => ∑ x ∈ blockOf M N' b.1, f x W) Z :=
      iteratedFDeriv_const_smul_apply
        (R := ℝ) (a := ((M : ℝ) ^ d)⁻¹) hsumSmooth
    _ = ((M : ℝ) ^ d)⁻¹ •
        ∑ x ∈ blockOf M N' b.1,
          iteratedFDeriv ℝ n (f x) Z := congrArg _ hsum
    _ = _ := rfl

/-- Exact third-order specialization of the normalized-sum identity. -/
theorem iteratedFDeriv_three_cmp98UbarLogAverage_eq_normalized_sum
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1) :
    iteratedFDeriv ℝ 3 (cmp98UbarLogAverage U b) Z =
      ((M : ℝ) ^ d)⁻¹ •
        ∑ x ∈ blockOf M N' b.1,
          iteratedFDeriv ℝ 3
            (fun W =>
              nearLog
                (cmp98UbarAmbientDeviationMatrix U b x W)) Z :=
  iteratedFDeriv_cmp98UbarLogAverage_eq_normalized_sum
    U b Z 3 hsmall

/-- Every positive jet through order three of the normalized logarithmic
block average inherits the physical pointwise budget without cardinality
loss. -/
theorem norm_iteratedFDeriv_cmp98UbarLogAverage_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r q : NNReal) (hZ : ‖Z‖ < r)
    (hq : (q : ℝ) < 1)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < q)
    (i : ℕ) (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    ‖iteratedFDeriv ℝ i (cmp98UbarLogAverage U b) Z‖ ≤
      cmp102SourceLocalNearLogThirdJetBudget
        (Nc := Nc) d M r q := by
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1 :=
    fun x hx => (hD x hx).trans hq
  rw [iteratedFDeriv_cmp98UbarLogAverage_eq_normalized_sum
    U b Z i hsmall]
  apply norm_normalized_block_sum_le
    (M := M) (N' := N')
    (E := PhysicalAmbientMatrixTangent d (M * N') Nc [×i]→L[ℝ]
      Matrix (Fin Nc) (Fin Nc) ℂ) b.1
  intro x hx
  exact
    norm_iteratedFDeriv_nearLog_cmp98UbarAmbientDeviationMatrix_le
      U b x hx Z r q hZ hq (hD x hx) i hi1 hi3

/-- The normalized logarithmic block average inherits the physical
pointwise third-jet budget without cardinality loss. -/
theorem norm_iteratedFDeriv_three_cmp98UbarLogAverage_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r q : NNReal) (hZ : ‖Z‖ < r)
    (hq : (q : ℝ) < 1)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < q) :
    ‖iteratedFDeriv ℝ 3 (cmp98UbarLogAverage U b) Z‖ ≤
      cmp102SourceLocalNearLogThirdJetBudget
        (Nc := Nc) d M r q :=
  norm_iteratedFDeriv_cmp98UbarLogAverage_le_sourceBudget
    U b Z r q hZ hq hD 3 (by omega) (by omega)

end

end YangMills.RG
