/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq220PhysicalPotential

/-!
# The two-layer resummation in CMP116 equation (2.19)

Equation (1.43) decays first in the localization domain `Y`.  After the
contour-radius choice (2.18), equation (2.19) retains two distinct weights:

* a domain weight proportional to
  `alpha4 * M⁻⁴ * exp (-(kappa1 - 1) * M⁻⁴ * |Y| / 4)`;
* an internal bond kernel
  `exp (-(kappa1 - 1) * M⁻¹ * |b₋ - b'₋| / 16)`.

This module keeps those layers separate.  The internal kernel is consumed by
Schur, while the domain weight is summed only over domains containing a fixed
root bond.  Consequently no total number of domains, ambient volume, or Lie
coordinate dimension appears.

Honest scope: the theorem starts from the literal majorant (2.19) and a rooted
domain-sum certificate.  Deriving those premises from (1.43), (2.18), and the
source definition of the localization family remains a separate obligation.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- The domain-size coefficient left in equation (2.19). -/
noncomputable def cmp116Eq219DomainAmplitude
    (alpha4 : ℝ) (M : ℕ) (kappa1 : ℝ) (domainCard : ℕ) : ℝ :=
  alpha4 * (((M : ℝ) ^ 4)⁻¹) *
    Real.exp (-(1 / 4 : ℝ) * (kappa1 - 1) *
      (((M : ℝ) ^ 4)⁻¹) * domainCard)

/-- The internal bond-decay rate left in equation (2.19). -/
noncomputable def cmp116Eq219InternalRate
    (M : ℕ) (kappa1 : ℝ) : ℝ :=
  (1 / 16 : ℝ) * (kappa1 - 1) * (M : ℝ)⁻¹

/-- Schur consumes only the internal bond-distance layer of (2.19). -/
theorem cmp116Eq219_internalSchur
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    (B : PhysicalGaugeOneCochain d N Nc)
    {amplitude rate rowSum : ℝ}
    (hamplitude : 0 ≤ amplitude)
    (hrow : ∀ target : PhysicalBond d N,
      ∑ source : PhysicalBond d N,
        Real.exp (-(rate * (physicalBondDist target source : ℝ))) ≤ rowSum) :
    ∑ target ∈ S, ∑ source ∈ S,
        amplitude *
          Real.exp (-(rate * (physicalBondDist target source : ℝ))) *
          ‖B target‖ * ‖B source‖ ≤
      (amplitude * rowSum) * ∑ i ∈ S, ‖B i‖ ^ 2 := by
  classical
  let u : PhysicalBond d N → ℝ :=
    fun i => if i ∈ S then ‖B i‖ else 0
  let K : PhysicalBond d N → PhysicalBond d N → ℝ :=
    fun target source =>
      amplitude *
        Real.exp (-(rate * (physicalBondDist target source : ℝ)))
  have hK : ExpDecay
      (fun target source => (physicalBondDist target source : ℝ))
      amplitude rate K := by
    intro target source
    dsimp [K]
    rw [abs_of_nonneg (mul_nonneg hamplitude (Real.exp_pos _).le)]
    simpa only [neg_mul] using
      (le_refl
        (amplitude *
          Real.exp (-(rate * (physicalBondDist target source : ℝ)))))
  have hschur := expDecay_quadratic_form_le
    hamplitude
    (fun target source => by
      exact_mod_cast physicalBondDist_comm target source)
    hK
    (fun target => by simpa only [neg_mul] using hrow target)
    u
  have hnonneg :
      0 ≤ ∑ target : PhysicalBond d N,
        ∑ source : PhysicalBond d N,
          u target * K target source * u source := by
    exact Finset.sum_nonneg fun target _ =>
      Finset.sum_nonneg fun source _ => by
        dsimp [u, K]
        split_ifs <;> positivity
  rw [abs_of_nonneg hnonneg] at hschur
  simpa [u, K, Finset.sum_ite_irrel, mul_ite, ite_mul,
    mul_assoc, mul_left_comm, mul_comm] using hschur

/-- The rooted-domain combinatorial exchange used after the internal Schur
bound.  A domain contributes only to roots contained in its support. -/
theorem cmp116Eq219_rootedEnergyResummation
    {Y I : Type*} [DecidableEq Y] [DecidableEq I]
    (D : Finset Y) (Y0 : Finset I)
    (support : Y → Finset I)
    (weight : Y → ℝ) (energy : I → ℝ)
    {rootBound : ℝ}
    (henergy : ∀ i ∈ Y0, 0 ≤ energy i)
    (hsubset : ∀ y ∈ D, support y ⊆ Y0)
    (hroot : ∀ i ∈ Y0,
      ∑ y ∈ D.filter (fun y => i ∈ support y), weight y ≤ rootBound) :
    ∑ y ∈ D, weight y * ∑ i ∈ support y, energy i ≤
      rootBound * ∑ i ∈ Y0, energy i := by
  classical
  have hsupportSum : ∀ y ∈ D,
      (∑ i ∈ support y, energy i) =
        ∑ i ∈ Y0, if i ∈ support y then energy i else 0 := by
    intro y hy
    calc
      (∑ i ∈ support y, energy i) =
          ∑ i ∈ Y0.filter (fun i => i ∈ support y), energy i := by
            apply Finset.sum_congr
            · ext i
              simp only [Finset.mem_filter]
              constructor
              · intro hi
                exact ⟨hsubset y hy hi, hi⟩
              · exact fun hi => hi.2
            · intro i _
              rfl
      _ = ∑ i ∈ Y0, if i ∈ support y then energy i else 0 := by
            rw [Finset.sum_filter]
  calc
    ∑ y ∈ D, weight y * ∑ i ∈ support y, energy i =
        ∑ y ∈ D, weight y *
          (∑ i ∈ Y0, if i ∈ support y then energy i else 0) := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [hsupportSum y hy]
    _ = ∑ i ∈ Y0,
        (∑ y ∈ D.filter (fun y => i ∈ support y), weight y) * energy i := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_filter]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hi : i ∈ support y <;> simp [hi]
    _ ≤ ∑ i ∈ Y0, rootBound * energy i := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (hroot i hi) (henergy i hi)
    _ = rootBound * ∑ i ∈ Y0, energy i := by
          rw [Finset.mul_sum]

/-- Source-faithful finite form of (2.19) -> (2.20).  The hypothesis
`hEq219` is precisely the displayed double-sum majorant, including its factor
`1/2`.  `hroot` then performs the domain-size resummation at a fixed bond. -/
theorem cmp116Eq219_rootedQuadraticResummation
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y) (Y0 : Finset (PhysicalBond d N))
    (support : Y → Finset (PhysicalBond d N))
    (amplitude : Y → ℝ)
    (B : PhysicalGaugeOneCochain d N Nc)
    {rate rowSum rootBound : ℝ}
    (hamplitude : ∀ y ∈ D, 0 ≤ amplitude y)
    (hrowSum : 0 ≤ rowSum)
    (hsubset : ∀ y ∈ D, support y ⊆ Y0)
    (hrow : ∀ target : PhysicalBond d N,
      ∑ source : PhysicalBond d N,
        Real.exp (-(rate * (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hroot : ∀ i ∈ Y0,
      ∑ y ∈ D.filter (fun y => i ∈ support y), amplitude y ≤ rootBound)
    (quadraticContribution : Y → ℝ)
    (hEq219 : ∀ y ∈ D,
      quadraticContribution y ≤
        (1 / 2 : ℝ) *
          ∑ target ∈ support y, ∑ source ∈ support y,
            amplitude y *
              Real.exp (-(rate *
                (physicalBondDist target source : ℝ))) *
              ‖B target‖ * ‖B source‖) :
    ∑ y ∈ D, quadraticContribution y ≤
      (rootBound * rowSum) / 2 * ∑ i ∈ Y0, ‖B i‖ ^ 2 := by
  have hperY : ∀ y ∈ D,
      quadraticContribution y ≤
        ((amplitude y * rowSum) / 2) *
          ∑ i ∈ support y, ‖B i‖ ^ 2 := by
    intro y hy
    refine (hEq219 y hy).trans ?_
    have hschur := cmp116Eq219_internalSchur
      (support y) B (hamplitude y hy) hrow
    nlinarith
  calc
    ∑ y ∈ D, quadraticContribution y ≤
        ∑ y ∈ D,
          ((amplitude y * rowSum) / 2) *
            ∑ i ∈ support y, ‖B i‖ ^ 2 :=
      Finset.sum_le_sum hperY
    _ = (rowSum / 2) *
        ∑ y ∈ D, amplitude y *
          ∑ i ∈ support y, ‖B i‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ (rowSum / 2) *
        (rootBound * ∑ i ∈ Y0, ‖B i‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (cmp116Eq219_rootedEnergyResummation
        D Y0 support amplitude (fun i => ‖B i‖ ^ 2)
        (fun i _ => sq_nonneg _) hsubset hroot)
        (div_nonneg hrowSum (by norm_num))
    _ = (rootBound * rowSum) / 2 *
        ∑ i ∈ Y0, ‖B i‖ ^ 2 := by ring

/-- Literal specialization of the rooted resummation to the two coefficients
printed in (2.19).  The domain cardinality is kept as an independent physical
datum; it is not replaced by the number of bonds in the domain. -/
theorem cmp116Eq219_literalRootedQuadraticResummation
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y) (Y0 : Finset (PhysicalBond d N))
    (support : Y → Finset (PhysicalBond d N))
    (domainCard : Y → ℕ)
    (alpha4 : ℝ) (M : ℕ) (kappa1 : ℝ)
    (B : PhysicalGaugeOneCochain d N Nc)
    {rowSum rootBound : ℝ}
    (hamplitude : ∀ y ∈ D,
      0 ≤ cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y))
    (hrowSum : 0 ≤ rowSum)
    (hsubset : ∀ y ∈ D, support y ⊆ Y0)
    (hrow : ∀ target : PhysicalBond d N,
      ∑ source : PhysicalBond d N,
        Real.exp (-(cmp116Eq219InternalRate M kappa1 *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hroot : ∀ i ∈ Y0,
      ∑ y ∈ D.filter (fun y => i ∈ support y),
        cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y) ≤ rootBound)
    (quadraticContribution : Y → ℝ)
    (hEq219 : ∀ y ∈ D,
      quadraticContribution y ≤
        (1 / 2 : ℝ) *
          ∑ target ∈ support y, ∑ source ∈ support y,
            cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y) *
              Real.exp (-(cmp116Eq219InternalRate M kappa1 *
                (physicalBondDist target source : ℝ))) *
              ‖B target‖ * ‖B source‖) :
    ∑ y ∈ D, quadraticContribution y ≤
      (rootBound * rowSum) / 2 * ∑ i ∈ Y0, ‖B i‖ ^ 2 := by
  exact cmp116Eq219_rootedQuadraticResummation
    D Y0 support
    (fun y => cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y))
    B hamplitude hrowSum hsubset hrow hroot quadraticContribution hEq219

end

end YangMills.RG
