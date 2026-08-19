/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This scratch file closes the phase algebra needed before transporting the
centered-torus Fourier coefficient to the literal fine-lattice Green.  The
reciprocal alias `p + 2*pi*m` contributes no extra phase at an integer
displacement; that fact is derived from the already sealed arbitrary-vector
physical-period theorem at `N = 1`.

The result is then lifted termwise through the literal bare and stabilized
Green numerators and finally through the common stabilized denominator.  No
integral equality, Fourier-coefficient theorem, Green bound, `B0`, window-15
attainment or terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointAliasPhase
import YangMills.RG.BalabanCMP89CenteredTorusFourierPhase
import YangMills.RG.BalabanCMP89Eq248FineLatticeFourierGreenLeftDerivative

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- A reciprocal alias `2*pi*m` is invisible to the exponential phase at an
integer lattice displacement.  This is the exact named bridge between the
base torus character and every alias branch of the physical Green. -/
theorem exp_I_cmp89Eq251EntireAliasPhase_latticeDisplacement
    {d : ℕ} (p : Fin d → ℂ) (m n : Fin d → ℤ) :
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum p m)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((1 : ℝ)⁻¹) n)) =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase p
        (cmp89Eq249PhysicalFineLatticeDisplacement ((1 : ℝ)⁻¹) n)) := by
  have hAlias :
      cmp89Eq248EntireAliasMomentum p m =
        fun mu => p mu + (m mu : ℂ) * (((2 * Real.pi : ℝ) : ℂ)) := by
    funext mu
    simp only [cmp89Eq248EntireAliasMomentum, cmp89Eq245AliasShift]
    push_cast
    ring
  rw [hAlias]
  simpa using
    (exp_I_cmp89Eq251EntirePhase_add_int_aliasPeriods_physicalFine
      (N := 1) p m n)

/-- Alias-aware orientation gate.  Mathlib's negative Fourier character and
the phase of every reciprocal-alias branch land at the same positive affine
displacement `(u + M*n)/M`. -/
theorem cmp89UnitAddTorus_mFourier_neg_mul_aliasFinePhase_eq_affineResiduePhase
    {d M : ℕ} (hM : 0 < M) (n u m : Fin d → ℤ)
    (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (-n)
          (fun mu ↦ ((t mu : ℝ) : UnitAddCircle)) *
        Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum
            (cmp89Eq248NegativeTwoPiTorusMomentum t) m)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248NegativeTwoPiTorusMomentum t) m)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu ↦ u mu + (M : ℤ) * n mu))) := by
  let p := cmp89Eq248NegativeTwoPiTorusMomentum t
  let q := cmp89Eq248EntireAliasMomentum p m
  have halias := exp_I_cmp89Eq251EntireAliasPhase_latticeDisplacement p m n
  have haffine := cmp89Eq251EntirePhase_physicalFine_affineResidue
    hM q u n
  rw [cmp89UnitAddTorus_mFourier_neg_eq_exp_physicalPhase]
  have halias' :
      Complex.exp (Complex.I * (∑ mu, p mu * (n mu : ℂ))) =
        Complex.exp (Complex.I * (∑ mu, q mu * (n mu : ℂ))) := by
    simpa [cmp89Eq251EntirePhase,
      cmp89Eq249PhysicalFineLatticeDisplacement] using halias.symm
  rw [halias', haffine, mul_add, Complex.exp_add]
  ring

/-- The alias-aware orientation gate lifted through one literal bare Green
numerator.  All non-phase factors remain definitionally unchanged. -/
theorem cmp89UnitAddTorus_mFourier_neg_mul_bareGreen_eq_affineResidue
    {d L j M : ℕ} (hM : 0 < M) (n u m : Fin d → ℤ)
    (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (-n)
          (fun mu ↦ ((t mu : ℝ) : UnitAddCircle)) *
        cmp89Eq248ComplexBareGreenEndpointNumerator d L j
          (cmp89Eq248NegativeTwoPiTorusMomentum t) m
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u) =
      cmp89Eq248ComplexBareGreenEndpointNumerator d L j
        (cmp89Eq248NegativeTwoPiTorusMomentum t) m
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu ↦ u mu + (M : ℤ) * n mu)) := by
  simp only [cmp89Eq248ComplexBareGreenEndpointNumerator]
  rw [← mul_assoc,
    cmp89UnitAddTorus_mFourier_neg_mul_aliasFinePhase_eq_affineResiduePhase hM]

/-- The Fourier character moves through the complete stabilized Green
numerator.  The proof distributes over the literal finite alias sum; it does
not replace that sum by a synthetic family. -/
theorem cmp89UnitAddTorus_mFourier_neg_mul_stabilizedGreenNumerator_eq_affineResidue
    {d L j M : ℕ} (hM : 0 < M) (mass : ℝ)
    (n u : Fin d → ℤ) (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (-n)
          (fun mu ↦ ((t mu : ℝ) : UnitAddCircle)) *
        cmp89Eq248ComplexStabilizedGreenEndpointNumerator d L j mass
          (cmp89Eq248NegativeTwoPiTorusMomentum t)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u) =
      cmp89Eq248ComplexStabilizedGreenEndpointNumerator d L j mass
        (cmp89Eq248NegativeTwoPiTorusMomentum t)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu ↦ u mu + (M : ℤ) * n mu)) := by
  have hbare (m : Fin d → ℤ) :=
    cmp89UnitAddTorus_mFourier_neg_mul_bareGreen_eq_affineResidue
      (L := L) (j := j) hM n u m t
  unfold cmp89Eq248ComplexStabilizedGreenEndpointNumerator
  rw [mul_add, hbare]
  congr 1
  calc
    UnitAddTorus.mFourier (-n)
          (fun mu ↦ ((t mu : ℝ) : UnitAddCircle)) *
        (cmp89Eq249CentralEntireFineSymbol d L j mass
            (cmp89Eq248NegativeTwoPiTorusMomentum t) *
          ∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
              (cmp89Eq249ZeroAlias d),
            cmp89Eq248ComplexBareGreenEndpointNumerator d L j
                (cmp89Eq248NegativeTwoPiTorusMomentum t) m
                (cmp89Eq249PhysicalFineLatticeDisplacement
                  ((M : ℝ)⁻¹) u) /
              cmp89Eq245EntireScaledLaplacianSymbol d
                (((L : ℝ) ^ j)⁻¹) mass
                (cmp89Eq248EntireAliasMomentum
                  (cmp89Eq248NegativeTwoPiTorusMomentum t) m)) =
      cmp89Eq249CentralEntireFineSymbol d L j mass
          (cmp89Eq248NegativeTwoPiTorusMomentum t) *
        (UnitAddTorus.mFourier (-n)
            (fun mu ↦ ((t mu : ℝ) : UnitAddCircle)) *
          ∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
              (cmp89Eq249ZeroAlias d),
            cmp89Eq248ComplexBareGreenEndpointNumerator d L j
                (cmp89Eq248NegativeTwoPiTorusMomentum t) m
                (cmp89Eq249PhysicalFineLatticeDisplacement
                  ((M : ℝ)⁻¹) u) /
              cmp89Eq245EntireScaledLaplacianSymbol d
                (((L : ℝ) ^ j)⁻¹) mass
                (cmp89Eq248EntireAliasMomentum
                  (cmp89Eq248NegativeTwoPiTorusMomentum t) m)) := by ring
    _ = cmp89Eq249CentralEntireFineSymbol d L j mass
          (cmp89Eq248NegativeTwoPiTorusMomentum t) *
        ∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
            (cmp89Eq249ZeroAlias d),
          UnitAddTorus.mFourier (-n)
                (fun mu ↦ ((t mu : ℝ) : UnitAddCircle)) *
            (cmp89Eq248ComplexBareGreenEndpointNumerator d L j
                (cmp89Eq248NegativeTwoPiTorusMomentum t) m
                (cmp89Eq249PhysicalFineLatticeDisplacement
                  ((M : ℝ)⁻¹) u) /
              cmp89Eq245EntireScaledLaplacianSymbol d
                (((L : ℝ) ^ j)⁻¹) mass
                (cmp89Eq248EntireAliasMomentum
                  (cmp89Eq248NegativeTwoPiTorusMomentum t) m)) := by
      rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      rw [← mul_div_assoc, hbare]

/-- The exact alias-aware phase transport for the literal stabilized Green
integrand.  The denominator is endpoint-independent and therefore unchanged. -/
theorem cmp89UnitAddTorus_mFourier_neg_mul_stabilizedGreen_eq_affineResidue
    {d L j M : ℕ} (hM : 0 < M) (mass a : ℝ)
    (n u : Fin d → ℤ) (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (-n)
          (fun mu ↦ ((t mu : ℝ) : UnitAddCircle)) *
        cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d L j mass a
          (cmp89Eq248NegativeTwoPiTorusMomentum t)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d L j mass a
        (cmp89Eq248NegativeTwoPiTorusMomentum t)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu ↦ u mu + (M : ℤ) * n mu)) := by
  unfold cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
  rw [← mul_div_assoc]
  rw [cmp89UnitAddTorus_mFourier_neg_mul_stabilizedGreenNumerator_eq_affineResidue
    hM]

end

end YangMills.RG
