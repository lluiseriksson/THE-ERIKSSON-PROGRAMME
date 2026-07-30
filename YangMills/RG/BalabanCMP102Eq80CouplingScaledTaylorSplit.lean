/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80CouplingScaledThirdJet
import YangMills.RG.BalabanCMP116RadialTaylorResidual

/-!
# Taylor split after the physical coupling substitution

The cutoff estimate acts on the Gaussian-coordinate potential

`B ↦ f (g_k C B)`,

not on the unscaled source potential `f`.  This file performs the exact
Taylor split after that substitution.  It proves internally that
normalization of `f` at the origin is preserved by the linear map
`g_k C`, and then separates:

* the radial quadratic operator frozen at zero;
* the genuine field-dependent radial residual.

No estimate is assumed or proved here.  In particular, this file does not
compare the residual with the equation-(1.36) majorant.  Its purpose is to
ensure that the residual controlled by the cutoff cubic theorem is exactly
the residual installed in the physical potential, rather than a similarly
typed unscaled object.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private abbrev CoupledField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev CoupledEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CoupledField M Q Nc →L[ℝ] CoupledField M Q Nc

/-- The quadratic operator of the coupling-scaled potential, frozen at the
zero Gaussian field. -/
noncomputable def cmp102Eq80CouplingScaledFixedQuadratic
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledField M Q Nc → ℝ)
    (hf : ContDiff ℝ 2 f) :
    CoupledEndomorphism M Q Nc :=
  cmp116RadialTaylorOperator
    (cmp102Eq80CouplingScaledPotential gk f) 0
    ((hf.comp
      (cmp109ConstrainedLinearFluctuationCLM
        (M := M) (Q := Q) (Nc := Nc) gk).contDiff).of_le
          (by norm_num))

/-- The scalar Taylor residual after the physical substitution `g_k C`.
This is the same residual operator that appears in the cutoff-centered cubic
bound. -/
noncomputable def cmp102Eq80CouplingScaledTaylorResidual
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledField M Q Nc → ℝ)
    (hf : ContDiff ℝ 2 f) (B : CoupledField M Q Nc) : ℝ :=
  (1 / 2 : ℝ) * inner ℝ B
    (cmp116RadialTaylorResidualOperator
      (cmp102Eq80CouplingScaledPotential gk f) B
      ((hf.comp
        (cmp109ConstrainedLinearFluctuationCLM
          (M := M) (Q := Q) (Nc := Nc) gk).contDiff).of_le
            (by norm_num)) B)

/-- A normalized source potential remains normalized after precomposition
with the physical linear fluctuation `g_k C`. -/
theorem hasFDerivAt_cmp102Eq80CouplingScaledPotential_zero
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledField M Q Nc → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hdf0 : fderiv ℝ f 0 = 0) :
    HasFDerivAt (cmp102Eq80CouplingScaledPotential gk f)
      (0 : CoupledField M Q Nc →L[ℝ] ℝ) 0 := by
  let L :=
    cmp109ConstrainedLinearFluctuationCLM
      (M := M) (Q := Q) (Nc := Nc) gk
  have hf0 :
      HasFDerivAt f
        (0 : CoupledField M Q Nc →L[ℝ] ℝ) 0 := by
    have h :
        HasFDerivAt f (fderiv ℝ f 0) 0 :=
      (hf.differentiable (by exact two_ne_zero)).differentiableAt.hasFDerivAt
    rw [hdf0] at h
    exact h
  have hfL0 :
      HasFDerivAt f
        (0 : CoupledField M Q Nc →L[ℝ] ℝ) (L 0) := by
    simpa using hf0
  have hcomp := hfL0.comp (0 : CoupledField M Q Nc) L.hasFDerivAt
  simpa [cmp102Eq80CouplingScaledPotential, L] using hcomp

/-- Exact fixed-quadratic plus Taylor-residual split after the physical
coupling substitution. -/
theorem cmp102Eq80CouplingScaledPotential_eq_fixed_add_residual
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledField M Q Nc → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0)
    (B : CoupledField M Q Nc) :
    cmp102Eq80CouplingScaledPotential gk f B =
      (1 / 2 : ℝ) * inner ℝ B
        (cmp102Eq80CouplingScaledFixedQuadratic gk f hf B) +
      cmp102Eq80CouplingScaledTaylorResidual gk f hf B := by
  let fscaled :=
    cmp102Eq80CouplingScaledPotential gk f
  have hfscaled : ContDiff ℝ 2 fscaled := by
    simpa [fscaled, cmp102Eq80CouplingScaledPotential] using
      hf.comp
        (cmp109ConstrainedLinearFluctuationCLM
          (M := M) (Q := Q) (Nc := Nc) gk).contDiff
  have hfscaled0 : fscaled 0 = 0 := by
    change f
      (cmp109ConstrainedLinearFluctuationCLM
        (M := M) (Q := Q) (Nc := Nc) gk 0) = 0
    rw [map_zero, hf0]
  have hdfscaled0 : fderiv ℝ fscaled 0 = 0 :=
    (hasFDerivAt_cmp102Eq80CouplingScaledPotential_zero
      gk f hf hdf0).fderiv
  simpa [
    fscaled,
    cmp102Eq80CouplingScaledFixedQuadratic,
    cmp102Eq80CouplingScaledTaylorResidual] using
      (cmp116RadialTaylorOperator_eq_fixed_add_residual_of_normalized
        fscaled B hfscaled hfscaled0 hdfscaled0)

end

end YangMills.RG
