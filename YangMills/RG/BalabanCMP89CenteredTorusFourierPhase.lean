/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This scratch file fixes the Fourier-sign convention for Step 8b.23.  The
Mathlib coefficient uses `mFourier (-n)` and the physical coarse momentum is
`p(t) = -2*pi*t`.  Their product must produce the positive affine
displacement `(u + M*n)/M`, with no Fourier negation and no parity factor.

No Fourier-series equality, Green bound, `B0`, window-15 attainment or
terminal field is asserted here.
-/

import Mathlib.Analysis.Fourier.AddCircleMulti
import YangMills.RG.BalabanCMP89Eq249FinePhaseScaleNoGo

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- Physical Brillouin momentum attached to a unit-torus representative.
The minus sign matches the literal CMP99 coarse amplitude momentum. -/
def cmp89Eq248NegativeTwoPiTorusMomentum
    {d : ℕ} (t : Fin d → ℝ) : Fin d → ℂ :=
  fun mu ↦ -((2 * Real.pi : ℝ) : ℂ) * (t mu : ℂ)

/-- Moving the integer Fourier frequency into a fine physical displacement
is an exact phase identity. -/
theorem cmp89Eq251EntirePhase_physicalFine_affineResidue
    {d M : ℕ} (hM : 0 < M) (p : Fin d → ℂ)
    (u n : Fin d → ℤ) :
    cmp89Eq251EntirePhase p
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu ↦ u mu + (M : ℤ) * n mu)) =
      cmp89Eq251EntirePhase p
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u) +
        ∑ mu, p mu * (n mu : ℂ) := by
  have hMC : (M : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hM
  unfold cmp89Eq251EntirePhase
    cmp89Eq249PhysicalFineLatticeDisplacement
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mu _
  push_cast
  field_simp [hMC]

/-- Mathlib's negative Fourier monomial is exactly the exponential of the
physical `p(t) dot n` phase in the chosen negative-momentum convention. -/
theorem cmp89UnitAddTorus_mFourier_neg_eq_exp_physicalPhase
    {d : ℕ} (n : Fin d → ℤ) (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (-n)
        (fun mu ↦ ((t mu : ℝ) : UnitAddCircle)) =
      Complex.exp (Complex.I *
        (∑ mu, cmp89Eq248NegativeTwoPiTorusMomentum t mu *
          (n mu : ℂ))) := by
  rw [UnitAddTorus.mFourier]
  simp only [ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  unfold cmp89Eq248NegativeTwoPiTorusMomentum
  push_cast
  ring

/-- Exact orientation gate for the physical Fourier coefficient.  The
character and endpoint phase land at the positive affine displacement
`(u + M*n)/M`. -/
theorem cmp89UnitAddTorus_mFourier_neg_mul_finePhase_eq_affineResiduePhase
    {d M : ℕ} (hM : 0 < M) (n u : Fin d → ℤ)
    (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (-n)
          (fun mu ↦ ((t mu : ℝ) : UnitAddCircle)) *
        Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248NegativeTwoPiTorusMomentum t)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248NegativeTwoPiTorusMomentum t)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu ↦ u mu + (M : ℤ) * n mu))) := by
  rw [cmp89UnitAddTorus_mFourier_neg_eq_exp_physicalPhase]
  rw [cmp89Eq251EntirePhase_physicalFine_affineResidue hM]
  rw [mul_add, Complex.exp_add]
  ring

end

end YangMills.RG
