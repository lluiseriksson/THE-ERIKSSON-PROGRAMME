/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249NormalizedStabilizedEndpointIntegralBound
import YangMills.RG.BalabanCMP89Eq251FineLatticeStabilizedEndpointBound
import YangMills.RG.BalabanCMP89Eq251FineLatticeStabilizedEndpointProductContourTelescope
import YangMills.RG.BalabanCMP89Eq251UnitLatticeHolderNormalization

/-!
# PRE-VALIDATION: normalized physical fine-lattice endpoint integral

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

CMP89 (2.49) places the physical endpoint on `(L^j)^(-1) Z^4` and the literal
factor `(2*pi)^(-4)` outside the Brillouin integral.  This module combines the
cold-sealed four-coordinate endpoint telescope with that existing exact
normalization and the source-faithful fine-lattice pointwise bound.

The neighbouring-endpoint comparison is also stated in physical units.  A
unit fine edge costs `exp (rho / L^j)`, not the unit-lattice `exp rho`.  The
scale is exposed in the theorem and is not absorbed into an amplitude.

This treats one endpoint.  Exact two-endpoint recombination, the physical
Fourier/operator dictionary, `B0`, window 15 and terminal fields remain open.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The physical spacing of the fine lattice used at CMP89 scale `j`. -/
def cmp89Eq249FineLatticeSpacing (L j : ℕ) : ℝ :=
  (((L ^ j : ℕ) : ℝ)⁻¹)

/-- The fine-lattice spacing is strictly positive when the block ratio is
nonzero. -/
theorem cmp89Eq249FineLatticeSpacing_pos
    (L j : ℕ) [NeZero L] : 0 < cmp89Eq249FineLatticeSpacing L j := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hpow : 0 < L ^ j := pow_pos hL j
  rw [cmp89Eq249FineLatticeSpacing]
  exact inv_pos.mpr (by exact_mod_cast hpow)

/-- Scaling an integer displacement by a nonnegative physical lattice spacing
scales its literal `l1` length by exactly that spacing. -/
theorem cmp89Eq251DisplacementL1_physicalFineLatticeDisplacement
    {d : ℕ} {xi : ℝ} (hxi : 0 ≤ xi) (u : Fin d → ℤ) :
    cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement xi u) =
      xi * cmp89Eq251LatticeL1Length u := by
  unfold cmp89Eq251DisplacementL1
    cmp89Eq249PhysicalFineLatticeDisplacement
  calc
    (∑ mu, |xi * (u mu : ℝ)|) =
        ∑ mu, xi * |(u mu : ℝ)| := by
      apply Finset.sum_congr rfl
      intro mu _
      rw [abs_mul, abs_of_nonneg hxi]
    _ = xi * ∑ mu, |(u mu : ℝ)| := by
      rw [Finset.mul_sum]
    _ = xi * cmp89Eq251LatticeL1Length u := by
      rw [← cmp89Eq251DisplacementL1_latticeDisplacement]
      rfl

/-- One stabilized endpoint integrated with the literal source normalization,
before its contour is moved. -/
def cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
    (L j : ℕ) [NeZero L] (mass a : ℝ) (mu : Fin 4)
    (holderU endpointU : Fin 4 → ℤ) : ℂ :=
  cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
    cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) holderU)
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) endpointU)

/-- The normalized physical endpoint integral equals its own independently
signed contour integral.  The equality is produced from the four-coordinate
telescope, not accepted as an input. -/
theorem cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_signed
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU endpointU : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
        L j mass a mu holderU endpointU =
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => cmp89Eq251ComplexStabilizedEndpointIntegrand
          4 L j mass a 0
          (cmp89Eq251SignedContourMomentum rho
            (cmp89Eq251PhysicalBrillouinParameter x)
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (cmp89Eq249FineLatticeSpacing L j) endpointU)) mu
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) holderU)
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) endpointU)) := by
  have h :=
    integral_cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_physicalFine_eq_signed
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass mu
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) holderU)
      endpointU
  unfold cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
    cmp89Eq249FourDimensionalBrillouinMeasure
  simpa [cmp89Eq249FineLatticeSpacing] using h

/-- The exact source-normalized physical endpoint bound.  No volume factor is
lost: the literal `(2*pi)^(-4)` cancels the translated cube volume. -/
theorem norm_cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU endpointU : Fin 4 → ℤ) :
    ‖cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
        L j mass a mu holderU endpointU‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) endpointU))) *
        cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho := by
  rw [cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_signed
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hmassPos hrho hamplitude hradius hwindow hmass]
  apply norm_cmp89Eq249NormalizedFourDimensionalBrillouinIntegral_le
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  let cube : Set (Fin 4 → ℝ) :=
    Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi)
  have hmeasure :
      cmp89Eq249FourDimensionalBrillouinMeasure =
        (volume : Measure (Fin 4 → ℝ)).restrict cube := by
    dsimp [cmp89Eq249FourDimensionalBrillouinMeasure, cube]
    rw [volume_pi, Measure.restrict_pi_pi]
    simp [Set.uIoc_of_le htwoPi]
  have hcube : MeasurableSet cube := by
    exact MeasurableSet.pi (Set.to_countable Set.univ) fun _ _ =>
      measurableSet_Ioc
  have hmem : ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure, x ∈ cube := by
    rw [hmeasure]
    exact ae_restrict_mem hcube
  filter_upwards [hmem] with x hx
  have hp : ∀ nu, |cmp89Eq251PhysicalBrillouinParameter x nu| ≤
      Real.pi := by
    intro nu
    have hxnu : x nu ∈ Set.Ioc 0 (2 * Real.pi) := hx nu (by simp)
    rw [abs_le]
    simp only [cmp89Eq251PhysicalBrillouinParameter]
    constructor <;> linarith [hxnu.1, hxnu.2, Real.pi_pos]
  exact
    norm_cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_signedContour_le
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hradius hmass hwindow hamplitude hp mu
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) holderU)
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) endpointU)

/-- The two fine-lattice endpoints of a unit bond differ by one physical edge.
The exact comparison cost is `exp (rho * (L^j)^(-1))`. -/
theorem exp_neg_cmp89Eq251DisplacementL1_physicalFine_transport_le
    {L j : ℕ} [NeZero L] {rho : ℝ} (hrho : 0 ≤ rho)
    {holder transport : Fin 4 → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holder) :
    Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) transport))) ≤
      Real.exp (rho * cmp89Eq249FineLatticeSpacing L j) *
        Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (fun mu => holder mu + transport mu)))) := by
  have hxi : 0 ≤ cmp89Eq249FineLatticeSpacing L j :=
    (cmp89Eq249FineLatticeSpacing_pos L j).le
  rw [cmp89Eq251DisplacementL1_physicalFineLatticeDisplacement hxi,
    cmp89Eq251DisplacementL1_physicalFineLatticeDisplacement hxi]
  have hlength :=
    cmp89Eq251LatticeL1Length_add_le_add_one_of_unit
      (holder := holder) (transport := transport) hunit
  have hscaled := mul_le_mul_of_nonneg_left hlength hxi
  have hexponent :
      -(rho * (cmp89Eq249FineLatticeSpacing L j *
        cmp89Eq251LatticeL1Length transport)) ≤
        rho * cmp89Eq249FineLatticeSpacing L j +
          -(rho * (cmp89Eq249FineLatticeSpacing L j *
            cmp89Eq251LatticeL1Length
              (fun mu => holder mu + transport mu))) := by
    nlinarith
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr hexponent

end

end YangMills.RG
