/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249FinePhaseScaleNoGo

/-!
# PRE-VALIDATION: physical fine-lattice Holder phase quotient

This source is present only as a static draft.  Its `.olean` has not been
materialized and none of the declarations below has been compiler-verified.

CMP89 (2.49) uses the physical displacement `xi * u`, not the integer vector
`u` itself.  The abstract phase estimate already accepts a real displacement;
the missing honest specialization is therefore to prove its denominator
strictly positive from the geometric data `0 < xi` and `u != 0`, rather than
accepting positivity as a renamed input.

The complete alias momentum remains explicit.  In particular this file does
not use the unit-lattice alias cancellation refuted by
`cmp89Eq249_halfScale_singleAliasPhase_ne_one`, define the local Holder
seminorm of CMP95 (1.109), sum aliases, construct a contour, produce `B0`,
attain window 15, discharge a terminal field or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- A nonzero integer displacement remains nonzero after multiplication by a
strictly positive physical lattice spacing. -/
theorem cmp89Eq249PhysicalFineLatticeDisplacement_ne_zero_draft
    {d : ℕ} {xi : ℝ} (hxi : 0 < xi) {u : Fin d → ℤ} (hu : u ≠ 0) :
    cmp89Eq249PhysicalFineLatticeDisplacement xi u ≠ 0 := by
  intro hzero
  apply hu
  funext mu
  have hcoord := congrFun hzero mu
  change xi * (u mu : ℝ) = 0 at hcoord
  have hcast : (u mu : ℝ) = 0 := (mul_eq_zero.mp hcoord).resolve_left hxi.ne'
  exact_mod_cast hcast

/-- Scaling a lattice displacement by the physical spacing scales the source
momentum square by exactly `xi^2`. -/
theorem cmp89Eq251MomentumSquare_physicalFineLatticeDisplacement_draft
    {d : ℕ} (xi : ℝ) (u : Fin d → ℤ) :
    cmp89Eq251MomentumSquare
        (cmp89Eq249PhysicalFineLatticeDisplacement xi u) =
      xi ^ 2 * cmp89Eq251MomentumSquare
        (cmp89Eq251LatticeDisplacement u) := by
  rw [cmp89Eq251MomentumSquare, cmp89Eq251MomentumSquare]
  unfold cmp89Eq249PhysicalFineLatticeDisplacement
    cmp89Eq251LatticeDisplacement
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]

/-- For a unit lattice bond and nonnegative spacing, the physical Euclidean
Holder denominator is exactly that spacing. -/
theorem cmp89Eq251EuclideanNorm_physicalFineLatticeDisplacement_eq_draft
    {d : ℕ} {xi : ℝ} (hxi : 0 ≤ xi) {u : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement u) :
    cmp89Eq251EuclideanNorm
        (cmp89Eq249PhysicalFineLatticeDisplacement xi u) = xi := by
  rw [cmp89Eq251EuclideanNorm,
    cmp89Eq251MomentumSquare_physicalFineLatticeDisplacement_draft,
    cmp89Eq251MomentumSquare_latticeDisplacement_eq_one_of_unit hunit,
    mul_one, Real.sqrt_sq_eq_abs, abs_of_nonneg hxi]

/-- The source Euclidean denominator is strictly positive for a nonzero
physical fine-lattice displacement.  No positivity witness is supplied by the
caller independently of the displacement. -/
theorem cmp89Eq251EuclideanNorm_physicalFineLatticeDisplacement_pos_draft
    {d : ℕ} {xi : ℝ} (hxi : 0 < xi) {u : Fin d → ℤ} (hu : u ≠ 0) :
    0 < cmp89Eq251EuclideanNorm
      (cmp89Eq249PhysicalFineLatticeDisplacement xi u) := by
  have hphysical :
      cmp89Eq249PhysicalFineLatticeDisplacement xi u ≠ 0 :=
    cmp89Eq249PhysicalFineLatticeDisplacement_ne_zero_draft hxi hu
  rw [cmp89Eq251EuclideanNorm]
  apply Real.sqrt_pos.2
  have hexists : ∃ mu, cmp89Eq249PhysicalFineLatticeDisplacement xi u mu ≠ 0 := by
    by_contra h
    push_neg at h
    apply hphysical
    funext mu
    exact h mu
  rcases hexists with ⟨mu, hmu⟩
  have hsq : 0 < cmp89Eq249PhysicalFineLatticeDisplacement xi u mu ^ 2 :=
    sq_pos_of_ne_zero hmu
  exact hsq.trans_le
    (Finset.single_le_sum
      (fun nu _ ↦ sq_nonneg
        (cmp89Eq249PhysicalFineLatticeDisplacement xi u nu))
      (Finset.mem_univ mu))

/-- Source-faithful specialization of the CMP89 Holder phase quotient to a
physical fine-lattice displacement.  The numerator still sees the complete
real alias momentum `p + 2*pi*m`; no alias phase is removed before its norm is
taken. -/
theorem norm_cmp89Eq249PhysicalFineLattice_phaseFactor_div_rpow_le_draft
    {d : ℕ} {xi alpha : ℝ} (hxi : 0 < xi)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (p : Fin d → ℝ) (m : Fin d → ℤ) {u : Fin d → ℤ} (hu : u ≠ 0) :
    let q : Fin d → ℝ := fun nu ↦ p nu + 2 * Real.pi * (m nu : ℝ)
    ‖Complex.exp (Complex.I * cmp89Eq251Phase q
        (cmp89Eq249PhysicalFineLatticeDisplacement xi u)) - 1‖ /
        cmp89Eq251EuclideanNorm
          (cmp89Eq249PhysicalFineLatticeDisplacement xi u) ^ alpha ≤
      2 * cmp89Eq251EuclideanNorm q ^ alpha := by
  dsimp only
  exact norm_cmp89Eq251_phaseFactor_div_displacement_rpow_le
    halpha0 halpha1
    (fun nu ↦ p nu + 2 * Real.pi * (m nu : ℝ))
    (cmp89Eq249PhysicalFineLatticeDisplacement xi u)
    (cmp89Eq251EuclideanNorm_physicalFineLatticeDisplacement_pos_draft
      hxi hu)

end

end YangMills.RG
