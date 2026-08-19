/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Arbitrary integer-vector physical periodicity for the literal displayed
Green.  The one-coordinate `2*pi` cycle is already sealed; this file turns it
into an integer shift with `Function.Periodic.int_mul_eq` and composes the
four coordinates explicitly.  Working at the displayed sum avoids borrowing
nonvanishing outside the centered strip.

No stabilized-domain theorem, finite sample identity, `B0`, window-15
attainment or terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP89Eq248GreenMassUniformHolomorphy

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- Shift one momentum coordinate by an arbitrary integer multiple of the
physical period `2*pi`. -/
def cmp89Eq248PhysicalCoordinateIntPeriodShift
    {d : ℕ} (nu : Fin d) (k : ℤ) (z : Fin d → ℂ) : Fin d → ℂ :=
  z + Pi.single nu ((k : ℂ) * ((2 * Real.pi : ℝ) : ℂ))

/-- The displayed fine-lattice Green is invariant under one arbitrary
integer coordinate period. -/
theorem cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_physicalFine_intPeriodShift_draft
    {d L j : ℕ} [NeZero L] (mass a : ℝ)
    (nu : Fin d) (k : ℤ) (z : Fin d → ℂ)
    (endpointU : Fin d → ℤ) :
    cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a
        (cmp89Eq248PhysicalCoordinateIntPeriodShift nu k z)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) := by
  let F : ℂ → ℂ := fun c =>
    cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a
      (z + Pi.single nu
        (c * ((2 * Real.pi : ℝ) : ℂ)))
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)
  have hperiod : Function.Periodic F 1 := by
    intro c
    have hone :=
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_physicalFinePeriodShift_draft
        (d := d) (L := L) (j := j) mass a nu
        (z + Pi.single nu
          (c * ((2 * Real.pi : ℝ) : ℂ))) endpointU
    have hshift :
        z + Pi.single nu
            ((c + 1) * ((2 * Real.pi : ℝ) : ℂ)) =
          cmp89Eq248PhysicalCoordinatePeriodShift nu
            (z + Pi.single nu
              (c * ((2 * Real.pi : ℝ) : ℂ))) := by
      funext mu
      simp [cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply]
      split_ifs <;> ring
    unfold F
    rw [hshift]
    exact hone
  have hk := hperiod.int_mul_eq k
  simpa [F, cmp89Eq248PhysicalCoordinateIntPeriodShift] using hk

/-- Coordinatewise integer physical-period shift. -/
def cmp89Eq248PhysicalVectorIntPeriodShift
    {d : ℕ} (w : Fin d → ℤ) (z : Fin d → ℂ) : Fin d → ℂ :=
  fun mu => z mu + (w mu : ℂ) * ((2 * Real.pi : ℝ) : ℂ)

/-- The displayed Green is invariant under an arbitrary integer vector of
physical periods.  The vector theorem is assembled from the sealed
coordinate periods by finite addition and integer multiplication. -/
theorem cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_physicalFine_vectorIntPeriodShift_draft
    {d L j : ℕ} [NeZero L] (mass a : ℝ)
    (w : Fin d → ℤ) (z : Fin d → ℂ)
    (endpointU : Fin d → ℤ) :
    cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a
        (cmp89Eq248PhysicalVectorIntPeriodShift w z)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) := by
  classical
  let F : (Fin d → ℂ) → ℂ := fun q =>
    cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a q
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)
  have hcoordinate : ∀ mu,
      Function.Periodic F
        (Pi.single mu (((2 * Real.pi : ℝ) : ℂ))) := by
    intro mu q
    simpa [F, cmp89Eq248PhysicalCoordinatePeriodShift] using
      (cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_physicalFinePeriodShift_draft
        (d := d) (L := L) (j := j) mass a mu q endpointU)
  have hsum : Function.Periodic F
      (∑ mu : Fin d,
        (w mu) • Pi.single mu (((2 * Real.pi : ℝ) : ℂ))) := by
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => simp [Function.Periodic]
    | @insert mu s hmu ih =>
        rw [Finset.sum_insert hmu]
        exact ((hcoordinate mu).zsmul (w mu)).add_period ih
  have hperiod := hsum z
  have hvector :
      z + (∑ mu : Fin d,
        (w mu) • Pi.single mu (((2 * Real.pi : ℝ) : ℂ))) =
        cmp89Eq248PhysicalVectorIntPeriodShift w z := by
    funext mu
    simp [cmp89Eq248PhysicalVectorIntPeriodShift, Pi.single_apply,
      zsmul_eq_mul]
  rw [hvector] at hperiod
  exact hperiod

end

end YangMills.RG
