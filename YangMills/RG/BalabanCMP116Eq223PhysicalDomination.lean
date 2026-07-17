/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq223GaussianDomination

/-!
# CMP116 equation (2.23): source-facing producers for `hdom`

The main Gaussian reduction accepts domination of the complete inner
equation-(2.14) integrand by the positive real Gaussian of (2.23). This
module proves that domination from the two inequalities that occur before
the Gaussian integration:

* an exponential-linear bound for the inner Wilson weight;
* a quadratic bound for the real part of the interaction exponent.

The literal small/large-field cutoffs disappear because their norm is at
most one. A second endpoint closes a nonzero exact quadratic-linear sector
without receiving `hdom` as a premise.

Honest scope: the interacting CMP116 inequalities (2.20)--(2.22) are not
proved here. The first theorem exposes them in their source-separated form;
the second theorem is an exact finite Gaussian sector.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

/-- The complete equation-(2.14) inner integrand is dominated by the real
Gaussian whenever its Wilson and interaction factors satisfy the separate
linear and quadratic source inequalities. -/
theorem CMP116Eq214AnalyticData.norm_innerIntegrand_le_realGaussian_of_bounds
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [Fintype B] [Norm E]
    (G : CMP116Eq214AnalyticData nDelta nY Bond X (B → ℝ) Ψ Φ E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ) (x : X) (b : B → ℝ)
    (A : Matrix B B ℝ) (r : B → ℝ)
    (hinner :
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r i * b i))
    (hinteraction :
      (G.interactionExponent sigma tau psi phi b).re ≤
        -((b ⬝ᵥ (A *ᵥ b)) / 2)) :
    ‖G.innerIntegrand Y0 P sigma tau psi phi x b‖ ≤
      cmp116Eq223RealGaussian A r b := by
  have h := G.norm_innerIntegrand_le Y0 P sigma tau psi phi x b
    (Real.exp (∑ i, r i * b i))
    (-((b ⬝ᵥ (A *ᵥ b)) / 2)) hinner hinteraction
  rw [cmp116Eq223RealGaussian]
  calc
    ‖G.innerIntegrand Y0 P sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r i * b i) *
          Real.exp (-((b ⬝ᵥ (A *ᵥ b)) / 2)) := h
    _ = Real.exp
        ((∑ i, r i * b i) + -((b ⬝ᵥ (A *ᵥ b)) / 2)) := by
          rw [Real.exp_add]
    _ = Real.exp
        (-((b ⬝ᵥ (A *ᵥ b)) / 2) + ∑ i, r i * b i) := by
          congr 1
          ring

/-- A nonzero exact quadratic-linear sector satisfies `hdom` outright.
The cutoff factor remains literal and may vanish on parts of configuration
space; no cutoff is replaced by one. -/
theorem CMP116Eq214AnalyticData.norm_innerIntegrand_le_realGaussian_of_exactSector
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [Fintype B] [Norm E]
    (G : CMP116Eq214AnalyticData nDelta nY Bond X (B → ℝ) Ψ Φ E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ) (x : X) (b : B → ℝ)
    (A : Matrix B B ℝ) (r : B → ℝ)
    (hinner : G.innerWeight sigma tau psi phi x b =
      Complex.exp ((∑ i, r i * b i : ℝ) : ℂ))
    (hinteraction : G.interactionExponent sigma tau psi phi b =
      ((-((b ⬝ᵥ (A *ᵥ b)) / 2) : ℝ) : ℂ)) :
    ‖G.innerIntegrand Y0 P sigma tau psi phi x b‖ ≤
      cmp116Eq223RealGaussian A r b := by
  apply G.norm_innerIntegrand_le_realGaussian_of_bounds
    Y0 P sigma tau psi phi x b A r
  · rw [hinner, Complex.norm_exp]
    simp
  · rw [hinteraction]
    simp

/-- Finite-Gaussian form of the exact-sector result. This is an explicit
producer of the almost-everywhere `hdom` premise consumed by the main
reduction theorem. -/
theorem CMP116Eq214FiniteGaussianData.ae_norm_innerIntegrand_le_realGaussian_of_exactSector
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim)
    (A : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
    (r : Bond × Fin lieDim → ℝ)
    (hinner : ∀ b, G.innerWeight sigma tau psi phi x b =
      Complex.exp ((∑ i, r i * b i : ℝ) : ℂ))
    (hinteraction : ∀ b, G.interactionExponent sigma tau psi phi b =
      ((-((b ⬝ᵥ (A *ᵥ b)) / 2) : ℝ) : ℂ)) :
    ∀ᵐ b ∂matrixGaussianPi (G.covarianceRoot sigma tau),
      ‖G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b‖ ≤
        cmp116Eq223RealGaussian A r b := by
  filter_upwards [] with b
  apply G.toAnalyticData.norm_innerIntegrand_le_realGaussian_of_exactSector
    Y0 P sigma tau psi phi x b A r
  · exact hinner b
  · exact hinteraction b

end

end YangMills.RG
