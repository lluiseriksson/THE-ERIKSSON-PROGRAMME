/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq136To220
import YangMills.RG.BalabanCMP116Eq214CauchyPolydisc
import YangMills.RG.BalabanCMP116Eq220ComplexPotential
import YangMills.RG.BalabanCMP116RadialTaylorBound

/-!
# Source-faithful equation (2.20) on centered Cauchy contours

The source Cauchy circle is centered at an interpolation point `s ∈ (0,1]`.
Consequently `(1.43)` and `(1.36)` cancel only against the displacement
`tau-s`, not against the full modulus `‖tau‖`.

This module keeps the two pieces separate:

* the interpolation center retains the literal source majorants;
* the displacement consumes the solved radius `(2.18)` and produces the
  printed `(2.19)`/`(2.20)` weights.

The terminal theorem constructs the radial equation-(1.42) operator
internally.  It assumes the literal radial Hessian estimate `(1.43)`, the
literal residual estimate `(1.36)`, exact support, and the physical metric
budget.  It does not assume an already assembled potential estimate.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- Center/displacement form of the source equation-(2.20) potential bound.

The first summand in each coefficient is the interpolation-center cost and
still contains `epsilon1`.  The second is the displacement amplitude printed
in `(2.19)`.  The residual ledger has the analogous two terms. -/
theorem cmp116Eq220_re_physicalComplexTauPotential_le_centeredSource
    {nY d N Nc : ℕ} [NeZero N]
    (D : Finset (Fin nY)) (Y0 : Finset (PhysicalBond d N))
    (tau : Fin nY → ℂ)
    (total residual :
      Fin nY → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore total residual y))
    (B : PhysicalGaugeOneCochain d N Nc)
    (kernelSupport :
      Fin nY → PhysicalBond d N → PhysicalBond d N → Prop)
    (domainDist : Fin nY → ℝ) (domainCard : Fin nY → ℕ)
    (E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa : ℝ)
    (M q : ℕ) (rowSum : ℝ)
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4)
    (hC3 : 0 ≤ C3) (hC3upper : C3 ≤ E0 * C1)
    (hM : 1 ≤ M) (hq : 8 ≤ q) (hkappa1 : 1 < kappa1)
    (hkappa :
      (1 - 3 * delta) * kappa ≤ (1 / 8 : ℝ) * (kappa1 - 1))
    (hdomainDist : ∀ y ∈ D, 0 ≤ domainDist y)
    (hcentered :
      CMP116Eq214CenteredPolydisc nY
        (fun y =>
          cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa (domainDist y))
        tau)
    (hrow : ∀ target : PhysicalBond d N,
      ∑ source : PhysicalBond d N,
        Real.exp (-(cmp116Eq219InternalRate M kappa1 *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hsupportB : ∀ i, i ∉ Y0 → B i = 0)
    (hgeometry : ∀ y ∈ D, ∀ source target,
      kernelSupport y source target →
        cmp116Eq219InternalRate M kappa1 *
            (physicalBondDist target source : ℝ) ≤
          (1 / 4 : ℝ) * (kappa1 - 1) *
            ((M : ℝ) ^ 4)⁻¹ * domainCard y)
    (hzero : ∀ y ∈ D, ∀ source target,
      ¬ kernelSupport y source target →
        ∀ (v w : SUNLieCoord Nc), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          cmp116FDerivHessian
            (cmp116Eq142PhysicalQuadraticCore total residual y)
            (t • B)
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) source v)
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) target w) = 0)
    (h143 : ∀ y ∈ D, ∀ source target (v w : SUNLieCoord Nc),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |cmp116FDerivHessian
          (cmp116Eq142PhysicalQuadraticCore total residual y)
          (t • B)
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v)
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) target w)| ≤
          cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
            (domainDist y) (domainCard y) * ‖v‖ * ‖w‖)
    (h136 : ∀ y ∈ D,
      |residual y B| ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa (domainDist y)) :
    (cmp116Eq214PhysicalComplexTauPotential D tau
        (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
        residual B).re ≤
      (∑ y ∈ D,
        (cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
            (domainDist y) (domainCard y) +
          cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
            rowSum) / 2 *
          (∑ i ∈ Y0, ‖B i‖ ^ 2) +
        ∑ y ∈ D,
          (cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
              C2 kappa1 delta kappa (domainDist y) +
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y)) := by
  let energy : ℝ := ∑ i ∈ Y0, ‖B i‖ ^ 2
  have hterm : ∀ y ∈ D,
      (tau y).re *
          cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B ≤
        ((cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
              (domainDist y) (domainCard y) +
            cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
              rowSum) / 2 * energy +
          (cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
              C2 kappa1 delta kappa (domainDist y) +
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y)) := by
    intro y hy
    obtain ⟨s, hs, htau⟩ := hcentered y
    let radius :=
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainDist y)
    let Qop :=
      cmp116Eq142PhysicalSourceQuadratic total residual hsmooth y B
    have hradius : 0 ≤ radius := by
      dsimp [radius, cmp116Eq218TauAbsSolved]
      positivity
    have hcenterKernel :
        PhysicalCovarianceExponentialKernelBound Qop physicalBondDist
          (cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
            (domainDist y) (domainCard y))
          (cmp116Eq219InternalRate M kappa1) := by
      dsimp [Qop]
      exact
        physicalCovarianceExponentialKernelBound_cmp116Eq142PhysicalSourceQuadratic_of_eq143_center
          total residual hsmooth y B physicalBondDist
          (kernelSupport y) C3 epsilon1 C2 kappa1
          (domainDist y) M (domainCard y) hC3 hepsilon1.le hM hkappa1
          (hgeometry y hy) (hzero y hy) (h143 y hy)
    have hdisplacementKernel :
        PhysicalCovarianceExponentialKernelBound (radius • Qop)
          physicalBondDist
          (cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y))
          (cmp116Eq219InternalRate M kappa1) := by
      dsimp [radius, Qop]
      apply
        physicalCovarianceExponentialKernelBound_smul_cmp116Eq142PhysicalSourceQuadratic_of_eq143
          total residual hsmooth y B physicalBondDist (kernelSupport y)
          E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa
          (domainDist y) M q (domainCard y)
          hE0 hepsilon1 hC1 halpha4 hC3 hC3upper hM hq hkappa1
      · intro source target hsupp
        apply cmp116Eq219_metricBudget_of_sourceConditions
          (hdomainDist y hy) hkappa
        simpa [cmp116Eq219InternalRate] using
          hgeometry y hy source target hsupp
      · exact hzero y hy
      · exact h143 y hy
    have hquadratic :=
      cmp116Eq220_centeredQuadratic_le_localized
        Y0 Qop B (cmp116Eq219InternalRate M kappa1) rowSum
        (cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
          (domainDist y) (domainCard y))
        (cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y))
        radius hs htau hradius hrow hsupportB hcenterKernel
        hdisplacementKernel
    have hremainder :=
      cmp116Eq136_centeredContour_residual_le
        hE0 hepsilon1 hC1 halpha4 hM hs htau
        (abs_nonneg (residual y B)) (h136 y hy)
    have hpotentialAbs :
        |cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B| ≤
          (1 / 2 : ℝ) * |inner ℝ B (Qop B)| + |residual y B| := by
      dsimp [cmp116Eq142PhysicalPotentialTerm, Qop]
      calc
        |(1 / 2 : ℝ) *
              inner ℝ B
                (cmp116Eq142PhysicalSourceQuadratic
                  total residual hsmooth y B B) +
            residual y B| ≤
          |(1 / 2 : ℝ) *
              inner ℝ B
                (cmp116Eq142PhysicalSourceQuadratic
                  total residual hsmooth y B B)| +
            |residual y B| := abs_add_le _ _
        _ = (1 / 2 : ℝ) *
              |inner ℝ B
                (cmp116Eq142PhysicalSourceQuadratic
                  total residual hsmooth y B B)| +
            |residual y B| := by norm_num [abs_mul]
    calc
      (tau y).re *
          cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B ≤
        |(tau y).re *
          cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B| := le_abs_self _
      _ = |(tau y).re| *
          |cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B| := abs_mul _ _
      _ ≤ ‖tau y‖ *
          ((1 / 2 : ℝ) * |inner ℝ B (Qop B)| + |residual y B|) := by
        exact mul_le_mul
          (Complex.abs_re_le_norm (tau y)) hpotentialAbs
          (abs_nonneg _)
          (le_trans (abs_nonneg _)
            (Complex.abs_re_le_norm (tau y)))
      _ = (1 / 2 : ℝ) * (‖tau y‖ * |inner ℝ B (Qop B)|) +
          ‖tau y‖ * |residual y B| := by ring
      _ ≤ (1 / 2 : ℝ) *
            ((cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
                (domainDist y) (domainCard y) +
              cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
                rowSum * energy) +
          (cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
              C2 kappa1 delta kappa (domainDist y) +
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hquadratic (by norm_num))
          hremainder
      _ =
        ((cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
              (domainDist y) (domainCard y) +
            cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
              rowSum) / 2 * energy +
          (cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
              C2 kappa1 delta kappa (domainDist y) +
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y)) := by ring
  have hsum := Finset.sum_le_sum hterm
  calc
    (cmp116Eq214PhysicalComplexTauPotential D tau
        (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
        residual B).re =
      ∑ y ∈ D,
        (tau y).re *
          cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B := by
      simp [cmp116Eq214PhysicalComplexTauPotential_re,
        cmp116Eq214PhysicalTauPotential]
    _ ≤ ∑ y ∈ D,
        (((cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
              (domainDist y) (domainCard y) +
            cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
              rowSum) / 2 * energy +
          (cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
              C2 kappa1 delta kappa (domainDist y) +
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y))) := hsum
    _ =
      (∑ y ∈ D,
        (cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
            (domainDist y) (domainCard y) +
          cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
            rowSum) / 2 * energy +
        ∑ y ∈ D,
          (cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
              C2 kappa1 delta kappa (domainDist y) +
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ y ∈ D,
          ((cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
                (domainDist y) (domainCard y) +
              cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
                rowSum) / 2 * energy) =
            ∑ y ∈ D,
              ((cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
                  (domainDist y) (domainCard y) +
                cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
                  rowSum) * (energy / 2) := by
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ =
          (∑ y ∈ D,
            (cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
                (domainDist y) (domainCard y) +
              cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
                rowSum) * (energy / 2) := by
          rw [Finset.sum_mul]
        _ =
          (∑ y ∈ D,
            (cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
                (domainDist y) (domainCard y) +
              cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
                rowSum) / 2 * energy := by ring

end

end YangMills.RG
