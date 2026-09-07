/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98CoarseContourQuadratic

/-!
# A derivative-free cross-term bound for the CMP98 two-factor block

For `B(t) = E(t) * C(t)`, the quadratic cross term can be written as the
product of the two displacements.  This avoids a separate norm estimate for
`E'(0)`, which would be an artificial obligation in the physical CMP98
application.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

local instance cmp98TwoFactorQuadraticMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Exact noncommutative two-factor Taylor identity. -/
theorem cmp98_twoFactor_sub_zero_sub_first_eq
    (Et E0 Ep Ct C0 Cp : Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ) :
    Et * Ct - E0 * C0 - t • (Ep * C0 + E0 * Cp) =
      (Et - E0 - t • Ep) * C0 +
        E0 * (Ct - C0 - t • Cp) +
        (Et - E0) * (Ct - C0) := by
  have hsmul : t • (Ep * C0 + E0 * Cp) =
      (t • Ep) * C0 + E0 * (t • Cp) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
      RCLike.real_smul_eq_coe_mul]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    ring
  rw [hsmul]
  noncomm_ring

/-- Norm form of the exact two-factor identity.  All five scalar inputs are
component estimates; no derivative norm is requested. -/
theorem norm_twoFactor_sub_zero_sub_first_le
    (Et E0 Ep Ct C0 Cp : Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ)
    (QE E0bound QC DE DC : ℝ)
    (hE2 : ‖Et - E0 - t • Ep‖ ≤ QE)
    (hE0 : ‖E0‖ ≤ E0bound)
    (hC2 : ‖Ct - C0 - t • Cp‖ ≤ QC)
    (hED : ‖Et - E0‖ ≤ DE)
    (hCD : ‖Ct - C0‖ ≤ DC)
    (hC0 : ‖C0‖ = 1) :
    ‖Et * Ct - E0 * C0 - t • (Ep * C0 + E0 * Cp)‖ ≤
      QE + E0bound * QC + DE * DC := by
  have hQE0 : 0 ≤ QE := (norm_nonneg _).trans hE2
  have hE0b0 : 0 ≤ E0bound := (norm_nonneg _).trans hE0
  have hDE0 : 0 ≤ DE := (norm_nonneg _).trans hED
  rw [cmp98_twoFactor_sub_zero_sub_first_eq]
  calc
    ‖(Et - E0 - t • Ep) * C0 + E0 * (Ct - C0 - t • Cp) +
          (Et - E0) * (Ct - C0)‖
        ≤ ‖(Et - E0 - t • Ep) * C0‖ +
            ‖E0 * (Ct - C0 - t • Cp)‖ +
            ‖(Et - E0) * (Ct - C0)‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖Et - E0 - t • Ep‖ * ‖C0‖ +
          ‖E0‖ * ‖Ct - C0 - t • Cp‖ +
          ‖Et - E0‖ * ‖Ct - C0‖ := by
      exact add_le_add
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        (norm_mul_le _ _)
    _ ≤ QE * 1 + E0bound * QC + DE * DC := by
      rw [hC0]
      exact add_le_add
        (add_le_add
          (mul_le_mul hE2 (le_refl 1) (by norm_num) hQE0)
          (mul_le_mul hE0 hC2 (norm_nonneg _) hE0b0))
        (mul_le_mul hED hCD (norm_nonneg _) hDE0)
    _ = QE + E0bound * QC + DE * DC := by ring

end

end YangMills.RG
