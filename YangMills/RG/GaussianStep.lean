/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# The free renormalization-group step on a Gaussian field (gauge-RG, UV-S2 brick G3)

`docs/UV-S2-GAUSSIAN-PLAN.md` G3.  The free (Gaussian) renormalization-group
step pushes a Gaussian bond field forward under the averaging operator
`Q` (a continuous linear map, `RG/AveragingL2.linAvgCLM`).  Two facts make
this tractable on Mathlib's `ProbabilityTheory.IsGaussian` framework:

* `isGaussian_map` (an instance): the pushforward of a Gaussian under a
  continuous linear map is Gaussian — so the coarse field is Gaussian;
* this file's **covariance transformation law**: the pushed-forward
  covariance bilinear form is the original one precomposed with `Q` on
  the dual, `Cov(μ.map Q)[L,L] = Cov(μ)[L∘Q, L∘Q]` — so the coarse
  covariance is `Q C Qᵀ`, whose ℓ²-scale is controlled by the proven
  operator contraction (`RG/AveragingL2.linAvg_l2_le/contraction`).

This is the **free fixed-point** half of S2; the interacting correction
(the gauge fluctuation integral) is the open analytic core (G5).

**Source.** Standard Gaussian calculus; the application is Bałaban's RG
(CMP 95–96).  Strategy/framing: Lluis Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

open MeasureTheory ProbabilityTheory

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] [CompleteSpace F]

/-- **Covariance transformation law of the free RG step** (UV-S2, brick
G3): pushing a Gaussian measure forward under a continuous linear map
`Q` transforms its covariance bilinear form by precomposition with `Q`
on the dual,
`covarianceBilinDual (μ.map Q) L L = covarianceBilinDual μ (L∘Q) (L∘Q)`.
Together with `isGaussian_map` (the pushforward is Gaussian) this is the
free renormalization-group step on the covariance: `C ↦ Q C Qᵀ`.  Proof:
the diagonal of the covariance form is the variance
(`covarianceBilinDual_self_eq_variance`), and variance pushes back under
the map (`variance_map`). -/
theorem covarianceBilinDual_map_clm (μ : Measure E) [IsGaussian μ]
    (Q : E →L[ℝ] F) (L : StrongDual ℝ F) :
    covarianceBilinDual (μ.map Q) L L
      = covarianceBilinDual μ (L.comp Q) (L.comp Q) := by
  rw [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id L,
    covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id (L.comp Q),
    variance_map (by fun_prop) (by fun_prop)]
  rfl

/-- **Free covariance contraction by `‖Q‖²`** (UV-S2, brick G4): if the
Gaussian `μ` has a covariance bound `Cov(μ)[M,M] ≤ B·‖M‖²` (the input
form of the Bałaban fluctuation-covariance bound `‖C_k‖ ≤ c·L²`, CMP 95
Prop 1.1/1.2 — see `docs/BALABAN-SOURCE-BOUNDS.md`), then the
pushed-forward covariance contracts by `‖Q‖²`,
`Cov(μ.map Q)[L,L] ≤ B·‖Q‖²·‖L‖²`.  This is the operator-norm form of the
free renormalization-group step `C ↦ Q C Qᵀ`: with the deterministic
operator bound `linAvg_l2_le` (giving `‖Q‖² ≤ L^{2-d}` at `Q = linAvgCLM`)
it yields the per-scale **free** covariance contraction.  From the
transformation law (`covarianceBilinDual_map_clm`) and
`‖L∘Q‖ ≤ ‖L‖·‖Q‖`. -/
theorem covarianceBilinDual_map_le (μ : Measure E) [IsGaussian μ]
    (Q : E →L[ℝ] F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ M : StrongDual ℝ E, covarianceBilinDual μ M M ≤ B * ‖M‖ ^ 2)
    (L : StrongDual ℝ F) :
    covarianceBilinDual (μ.map Q) L L ≤ B * ‖Q‖ ^ 2 * ‖L‖ ^ 2 := by
  rw [covarianceBilinDual_map_clm]
  have hcomp : ‖L.comp Q‖ ≤ ‖L‖ * ‖Q‖ := ContinuousLinearMap.opNorm_comp_le L Q
  calc covarianceBilinDual μ (L.comp Q) (L.comp Q)
      ≤ B * ‖L.comp Q‖ ^ 2 := hB (L.comp Q)
    _ ≤ B * (‖L‖ * ‖Q‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcomp 2) hB0
    _ = B * ‖Q‖ ^ 2 * ‖L‖ ^ 2 := by ring

end YangMills.RG
