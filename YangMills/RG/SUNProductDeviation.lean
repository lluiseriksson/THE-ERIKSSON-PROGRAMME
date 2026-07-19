/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.SUNMatrixRealization
import YangMills.ClayCore.WilsonLine

/-!
# Volume-free deviation bounds for products of special-unitary links

The distance of an ordered product from the identity is bounded by the sum of
the distances of its factors.  This is the exact finite-product telescoping
estimate needed by the physical CMP99 Ubar deviation.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

local instance matrixL2CStarAlgebraForSUNProduct :
    CStarAlgebra (Matrix (Fin Nc) (Fin Nc) ℂ) where

/-- Left multiplication by a physical special-unitary matrix is contractive
in the L2 operator norm. -/
theorem norm_sun_mul_matrix_le (U : SUN Nc)
    (X : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) * X‖ ≤ ‖X‖ := by
  calc
    ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) * X‖
        ≤ ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ)‖ * ‖X‖ := norm_mul_le _ _
    _ = 1 * ‖X‖ := by
      rw [show ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ)‖ = 1 by
        simpa only [specialUnitaryToUnitary_coe] using
          CStarRing.norm_coe_unitary (specialUnitaryToUnitary U)]
    _ = ‖X‖ := one_mul _

set_option maxHeartbeats 800000 in
/-- Two-factor telescoping estimate in the defining representation. -/
lemma norm_sun_mul_sub_one_le (U V : SUN Nc) :
    ‖((U * V : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
      ‖(V : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ := by
  change ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) *
      (V : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ _
  have hid :
      (U : Matrix (Fin Nc) (Fin Nc) ℂ) *
          (V : Matrix (Fin Nc) (Fin Nc) ℂ) - 1 =
        (U : Matrix (Fin Nc) (Fin Nc) ℂ) *
            ((V : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) +
          ((U : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) := by
    simp only [mul_sub, mul_one]
    abel
  have hnormU : ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ)‖ = 1 := by
    simpa only [specialUnitaryToUnitary_coe] using
      CStarRing.norm_coe_unitary (specialUnitaryToUnitary U)
  rw [hid]
  calc
    ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) *
          ((V : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) +
        ((U : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖
        ≤ ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) *
            ((V : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ +
          ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ := norm_add_le _ _
    _ ≤ ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ)‖ *
          ‖(V : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
          ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ :=
      add_le_add (norm_mul_le _ _) (le_refl _)
    _ = ‖(V : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
          ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ := by
      rw [hnormU, one_mul]
    _ = _ := add_comm _ _

/-- Inversion does not change the distance of a special-unitary matrix from
the identity. -/
theorem norm_sun_inv_sub_one_le (U : SUN Nc) :
    ‖((U⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ := by
  have hid :
      ((U⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1 =
        ((U⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) *
          (1 - (U : Matrix (Fin Nc) (Fin Nc) ℂ)) := by
    rw [mul_sub, mul_one]
    have hinv :
        ((U⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) *
          (U : Matrix (Fin Nc) (Fin Nc) ℂ) = 1 := by
      exact congrArg Subtype.val (inv_mul_cancel U)
    rw [hinv]
  rw [hid]
  calc
    ‖((U⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) *
        (1 - (U : Matrix (Fin Nc) (Fin Nc) ℂ))‖
        ≤ ‖1 - (U : Matrix (Fin Nc) (Fin Nc) ℂ)‖ :=
          norm_sun_mul_matrix_le U⁻¹
            (1 - (U : Matrix (Fin Nc) (Fin Nc) ℂ))
    _ = ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ := by
      rw [← neg_sub, norm_neg]

/-- Inversion does not change the distance of a special-unitary matrix from
the identity. -/
theorem norm_sun_inv_sub_one (U : SUN Nc) :
    ‖((U⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ =
      ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ := by
  apply le_antisymm
  · exact norm_sun_inv_sub_one_le U
  · simpa only [inv_inv] using norm_sun_inv_sub_one_le U⁻¹

variable {d N : ℕ} [FiniteLatticeGeometry d N (SUN Nc)]

/-- A Wilson line is no farther from the identity than the sum of the link
deviations along its literal ordered edge list. -/
theorem norm_wilsonLine_sub_one_le_sum
    (A : GaugeConfig d N (SUN Nc))
    (es : List (FiniteLatticeGeometry.E
      (d := d) (N := N) (G := SUN Nc))) :
    ‖((wilsonLine A es : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      (es.map fun e =>
        ‖(A e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖).sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
      rw [wilsonLine_cons, List.map_cons, List.sum_cons]
      exact (norm_sun_mul_sub_one_le (A e) (wilsonLine A es)).trans
        (add_le_add (le_refl _) ih)

/-- Uniform per-link smallness gives the exact path-length factor. -/
theorem norm_wilsonLine_sub_one_le_length_mul
    (A : GaugeConfig d N (SUN Nc))
    (es : List (FiniteLatticeGeometry.E
      (d := d) (N := N) (G := SUN Nc)))
    (ε : ℝ)
    (hsmall : ∀ e ∈ es,
      ‖(A e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ ε) :
    ‖((wilsonLine A es : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      (es.length : ℝ) * ε := by
  induction es with
  | nil => simp
  | cons e es ih =>
      calc
        ‖((wilsonLine A (e :: es) : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖
            ≤ ‖(A e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
              ‖((wilsonLine A es : SUN Nc) :
                Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ := by
              rw [wilsonLine_cons]
              exact norm_sun_mul_sub_one_le (A e) (wilsonLine A es)
        _ ≤ ε + (es.length : ℝ) * ε :=
          add_le_add (hsmall e (by simp))
            (ih (fun e' he' => hsmall e' (by simp [he'])))
        _ = ((e :: es).length : ℝ) * ε := by
          simp [Nat.cast_add, add_mul, add_comm]

end

end YangMills.RG
