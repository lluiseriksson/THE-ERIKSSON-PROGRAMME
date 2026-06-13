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

end YangMills.RG
