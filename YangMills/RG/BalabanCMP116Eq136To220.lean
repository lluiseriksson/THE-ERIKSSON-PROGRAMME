/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq143To219
import YangMills.RG.BalabanCMP116Eq220PhysicalPotential

/-!
# From the CMP116 residual estimate (1.36) to equation (2.20)

Equation (1.36) bounds the source residual `V''_k(Y,B)`.  Multiplication by
the contour radius fixed in (2.18) cancels the factors
`E0 * epsilon1 * C1 * M^q * exp (C2 * kappa1)` exactly and leaves

`alpha4 * exp (-delta * kappa * d_k(Y))`.

This file proves only that exact scalar cancellation and its immediate
pointwise consequence.  It deliberately does **not** manufacture a residual:
the concrete construction of `V''_k` and the proof that it satisfies (1.36)
remain the source-facing analytic obligation.
-/

namespace YangMills.RG

noncomputable section

/-- The literal right-hand side of the residual estimate (1.36). -/
noncomputable def cmp116Eq136ResidualMajorant
    (E0 epsilon1 C1 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa domainDist : ℝ) : ℝ :=
  E0 * epsilon1 * C1 * (M : ℝ) ^ q *
    Real.exp (C2 * kappa1) *
    Real.exp (-((1 - 2 * delta) * kappa * domainDist))

/-- The residual weight left in (2.20) after applying the `tau(Y)` contour
radius from (2.18). -/
noncomputable def cmp116Eq220ResidualDomainWeight
    (alpha4 delta kappa domainDist : ℝ) : ℝ :=
  alpha4 * Real.exp (-(delta * kappa * domainDist))

/-- Exact cancellation of the source constants between (1.36) and (2.18).
Only the factors that are cancelled are required to be nonzero. -/
theorem cmp116Eq218TauAbsSolved_mul_eq136ResidualMajorant
    {E0 epsilon1 C1 alpha4 C2 kappa1 delta kappa domainDist : ℝ}
    {M q : ℕ}
    (hE0 : E0 ≠ 0) (hepsilon1 : epsilon1 ≠ 0)
    (hC1 : C1 ≠ 0) (hM : M ≠ 0) :
    cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainDist *
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa domainDist =
      cmp116Eq220ResidualDomainWeight alpha4 delta kappa domainDist := by
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  unfold cmp116Eq218TauAbsSolved cmp116Eq136ResidualMajorant
    cmp116Eq220ResidualDomainWeight
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  calc
    alpha4 * Real.exp ((1 - 3 * delta) * kappa * domainDist) *
          Real.exp (-(kappa * domainDist * (1 - delta * 2))) =
        alpha4 *
          (Real.exp ((1 - 3 * delta) * kappa * domainDist) *
            Real.exp (-(kappa * domainDist * (1 - delta * 2)))) := by ring
    _ = alpha4 * Real.exp
        (((1 - 3 * delta) * kappa * domainDist) +
          (-(kappa * domainDist * (1 - delta * 2)))) := by
      rw [Real.exp_add]
    _ = alpha4 * Real.exp (-(delta * kappa * domainDist)) := by
      congr 2
      ring

/-- A genuine (1.36) estimate for a specified residual yields the exact
domain weight consumed by (2.20).  The hypothesis is intentionally named and
shaped as (1.36), rather than as an already assembled (2.20) remainder. -/
theorem cmp116Eq136_bound_mul_tauAbsSolved_le_eq220ResidualDomainWeight
    {E0 epsilon1 C1 alpha4 C2 kappa1 delta kappa domainDist residualAbs : ℝ}
    {M q : ℕ}
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (h136 : residualAbs ≤
      cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
        C2 kappa1 delta kappa domainDist) :
    cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainDist * residualAbs ≤
      cmp116Eq220ResidualDomainWeight alpha4 delta kappa domainDist := by
  have htau_nonneg : 0 ≤
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa domainDist := by
    unfold cmp116Eq218TauAbsSolved
    positivity
  calc
    cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainDist * residualAbs ≤
        cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainDist *
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa domainDist :=
      mul_le_mul_of_nonneg_left h136 htau_nonneg
    _ = cmp116Eq220ResidualDomainWeight alpha4 delta kappa domainDist :=
      cmp116Eq218TauAbsSolved_mul_eq136ResidualMajorant
        hE0.ne' hepsilon1.ne' hC1.ne' (Nat.ne_of_gt hM)

/-- Correct residual estimate on an actual source Cauchy circle.

The printed cancellation controls the displacement `‖z-s‖` by the solved
radius.  The interpolation center contributes one additional copy of the
literal `(1.36)` majorant; it is not silently absorbed into the `(2.20)`
weight. -/
theorem cmp116Eq136_centeredContour_residual_le
    {E0 epsilon1 C1 alpha4 C2 kappa1 delta kappa domainDist residualAbs : ℝ}
    {M q : ℕ} {s : ℝ} {z : ℂ}
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (hs : s ∈ Set.uIoc (0 : ℝ) 1)
    (hz : ‖z - (s : ℂ)‖ ≤
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa domainDist)
    (hresidual : 0 ≤ residualAbs)
    (h136 : residualAbs ≤
      cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
        C2 kappa1 delta kappa domainDist) :
    ‖z‖ * residualAbs ≤
      cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa domainDist +
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa domainDist := by
  have hs0 : 0 < s := by simpa using hs.1
  have hs1 : s ≤ 1 := by simpa using hs.2
  have hcenter : ‖(s : ℂ)‖ ≤ 1 := by
    simpa [abs_of_pos hs0] using hs1
  have hznorm :
      ‖z‖ ≤
        1 + cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainDist := by
    calc
      ‖z‖ = ‖(z - (s : ℂ)) + (s : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (s : ℂ)‖ + ‖(s : ℂ)‖ := norm_add_le _ _
      _ ≤
          cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
              C2 kappa1 delta kappa domainDist + 1 :=
        add_le_add hz hcenter
      _ = 1 + cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainDist := by ring
  have htau : 0 ≤
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa domainDist := by
    unfold cmp116Eq218TauAbsSolved
    positivity
  calc
    ‖z‖ * residualAbs ≤
        (1 + cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainDist) * residualAbs :=
      mul_le_mul_of_nonneg_right hznorm hresidual
    _ ≤
        (1 + cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainDist) *
          cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
            C2 kappa1 delta kappa domainDist := by
      exact mul_le_mul_of_nonneg_left h136
        (add_nonneg (by norm_num) htau)
    _ =
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
            C2 kappa1 delta kappa domainDist +
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa domainDist := by
      rw [add_mul, one_mul,
        cmp116Eq218TauAbsSolved_mul_eq136ResidualMajorant
          hE0.ne' hepsilon1.ne' hC1.ne' (Nat.ne_of_gt hM)]

/-- Equation (2.20) with the arbitrary `residualWeight` interface removed.
The only residual premise left is the literal source estimate (1.36), while
the contour modulus is fixed by (2.18); their product is generated internally.
This theorem still does not prove (1.36) for the concrete CMP116 residual. -/
theorem cmp116Eq220_physicalTauPotential_le_localized_of_eq136
    {Y : Type*} [DecidableEq Y]
    {d N Nc : ℕ} [NeZero N]
    (D : Finset Y) (Y0 : Finset (PhysicalBond d N))
    (domainDist : Y → ℝ) (tau : Y → ℝ)
    (quadratic : Y → PhysicalGaugeOneCochain d N Nc →
      (PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc))
    (remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (amplitude : Y → ℝ)
    {E0 epsilon1 C1 alpha4 C2 kappa1 delta kappa : ℝ}
    {M q : ℕ} {potentialKappa rowSum : ℝ}
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (htau : ∀ y ∈ D, |tau y| =
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainDist y))
    (hrow : ∀ target : PhysicalBond d N,
      ∑ source : PhysicalBond d N,
        Real.exp (-(potentialKappa *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (B : PhysicalGaugeOneCochain d N Nc)
    (hsupport : ∀ i, i ∉ Y0 → B i = 0)
    (hquadratic : ∀ y ∈ D,
      PhysicalCovarianceExponentialKernelBound
        (quadratic y B) physicalBondDist (amplitude y) potentialKappa)
    (h136 : ∀ y ∈ D,
      |remainder y B| ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa (domainDist y)) :
    cmp116Eq214PhysicalTauPotential D tau quadratic remainder B ≤
      (∑ y ∈ D, |tau y| * amplitude y * rowSum) / 2 *
          (∑ i ∈ Y0, ‖B i‖ ^ 2) +
        ∑ y ∈ D,
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) := by
  apply cmp116Eq220_physicalTauPotential_le_localized
    D Y0 tau quadratic remainder amplitude
      (fun y => cmp116Eq220ResidualDomainWeight alpha4 delta kappa
        (domainDist y)) hrow B hsupport hquadratic
  intro y hy
  rw [htau y hy]
  exact cmp116Eq136_bound_mul_tauAbsSolved_le_eq220ResidualDomainWeight
    hE0 hepsilon1 hC1 halpha4 hM (h136 y hy)

/-- Rooted resummation of the residual-domain weights in (2.20).  Every
domain is charged to at least one coarse block of its support; the rooted
domain sum then yields a local-volume cost, rather than a volume-wide one. -/
theorem cmp116Eq136_rootedResidualResummation
    {Y I : Type*} [DecidableEq Y] [DecidableEq I]
    (D : Finset Y) (Y0 : Finset I)
    (support : Y → Finset I) (weight : Y → ℝ)
    {rootBound : ℝ}
    (hweight : ∀ y ∈ D, 0 ≤ weight y)
    (hne : ∀ y ∈ D, (support y).Nonempty)
    (hsub : ∀ y ∈ D, support y ⊆ Y0)
    (hroot : ∀ i ∈ Y0,
      ∑ y ∈ D.filter (fun y => i ∈ support y), weight y ≤ rootBound) :
    ∑ y ∈ D, weight y ≤ rootBound * (Y0.card : ℝ) := by
  calc
    (∑ y ∈ D, weight y) ≤
        ∑ y ∈ D, weight y * ∑ _i ∈ support y, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro y hy
      have hcard : 1 ≤ ((support y).card : ℝ) := by
        exact_mod_cast Finset.one_le_card.mpr (hne y hy)
      simpa using le_mul_of_one_le_right (hweight y hy) hcard
    _ ≤ rootBound * ∑ _i ∈ Y0, (1 : ℝ) :=
      cmp116Eq219_rootedEnergyResummation
        D Y0 support weight (fun _ => (1 : ℝ))
          (fun _ _ => by norm_num) hsub hroot
    _ = rootBound * (Y0.card : ℝ) := by simp

/-- Literal residual-weight specialization of the rooted (2.20) resummation.
The remaining `hroot` premise is now exactly the source domain-counting fact;
it contains no field, residual, or post-Cauchy majorant. -/
theorem cmp116Eq220_residualDomainWeight_sum_le_localVolume
    {Y I : Type*} [DecidableEq Y] [DecidableEq I]
    (D : Finset Y) (Y0 : Finset I)
    (support : Y → Finset I) (domainDist : Y → ℝ)
    {alpha4 delta kappa rootBound : ℝ}
    (halpha4 : 0 ≤ alpha4)
    (hne : ∀ y ∈ D, (support y).Nonempty)
    (hsub : ∀ y ∈ D, support y ⊆ Y0)
    (hroot : ∀ i ∈ Y0,
      ∑ y ∈ D.filter (fun y => i ∈ support y),
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) ≤ rootBound) :
    ∑ y ∈ D,
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa
          (domainDist y) ≤
      rootBound * (Y0.card : ℝ) := by
  apply cmp116Eq136_rootedResidualResummation
    D Y0 support
      (fun y => cmp116Eq220ResidualDomainWeight alpha4 delta kappa
        (domainDist y))
  · intro y hy
    exact mul_nonneg halpha4 (Real.exp_nonneg _)
  · exact hne
  · exact hsub
  · exact hroot

end

end YangMills.RG
