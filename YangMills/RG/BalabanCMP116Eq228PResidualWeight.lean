/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq228DomainProduct
import YangMills.RG.BalabanCMP116Eq231PBondFactorBridge

/-!
# The literal post-domain residual entering the CMP116 P-sum

Equation (2.28) leaves one domain residual.  Before the equation-(2.31)
resummation this residual is multiplied by the literal large-field bond
factor from equation (2.26).  The definition below records precisely that
source product and connects it both to the raw domain ledger and to the
pointwise P-stage interface.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- The literal residual after the domain extraction and before summing `P`. -/
def cmp116Eq228PResidualWeight
    {ιP : Type*}
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa unionMetric : ℝ)
    (gamma2 gapEpsilon1 gk : ℝ) (pBonds : Finset ιP) : ℝ :=
  cmp116Eq228Residual
      E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
      delta kappa unionMetric *
    cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds

theorem cmp116Eq228PResidualWeight_nonneg
    {ιP : Type*}
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa unionMetric : ℝ)
    (gamma2 gapEpsilon1 gk : ℝ) (pBonds : Finset ιP)
    (hcoeff :
      0 ≤
        cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1) :
    0 ≤
      cmp116Eq228PResidualWeight
        E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
        delta kappa unionMetric gamma2 gapEpsilon1 gk pBonds := by
  unfold cmp116Eq228PResidualWeight cmp116Eq228Residual
    cmp116Eq226PBondFactor
  positivity

/-- The raw equation-(2.26) domain and bond factors are bounded by the
equation-(2.29) product times the literal post-domain residual. -/
theorem cmp116Eq226DomainProduct_mul_PBondFactor_le_eq229Product_mul_eq228PResidual
    {ιY ιP : Type*} [DecidableEq ιY]
    (D : Finset ιY) (hD : D.Nonempty)
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (domainMetric : ιY → ℕ) (unionMetric : ℝ)
    (gamma2 gapEpsilon1 gk : ℝ) (pBonds : Finset ιP)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 < alpha4)
    (halpha6 : 0 < alpha6)
    (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa)
    (hfourDelta : 4 * delta ≤ 1)
    (hsmall :
      cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 *
        Real.exp (5 * kappa) ≤ 1)
    (hEq227 :
      unionMetric + 5 ≤
        ∑ Y ∈ D, ((domainMetric Y : ℝ) + 5)) :
    cmp116Eq226DomainProduct
          E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
          domainMetric D *
        cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds ≤
      (∏ Y ∈ D,
          cmp116Eq229Weight alpha6 delta kappa domainMetric Y) *
        cmp116Eq228PResidualWeight
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa unionMetric gamma2 gapEpsilon1 gk pBonds := by
  have hdomain :=
    cmp116Eq226DomainProduct_le_eq229Product_mul_eq228Residual
      D hD E0 epsilon1 C1 alpha4 alpha6 M q
      C2 kappa1 delta kappa domainMetric unionMetric
      hE0 hepsilon1 hC1 halpha4 halpha6
      hdelta hkappa hfourDelta hsmall hEq227
  calc
    cmp116Eq226DomainProduct
          E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
          domainMetric D *
        cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds ≤
      ((∏ Y ∈ D,
          cmp116Eq229Weight alpha6 delta kappa domainMetric Y) *
        cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa unionMetric) *
        cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds := by
      exact mul_le_mul_of_nonneg_right hdomain
        (by
          unfold cmp116Eq226PBondFactor
          positivity)
    _ =
      (∏ Y ∈ D,
          cmp116Eq229Weight alpha6 delta kappa domainMetric Y) *
        cmp116Eq228PResidualWeight
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa unionMetric gamma2 gapEpsilon1 gk pBonds := by
      unfold cmp116Eq228PResidualWeight
      ring

/-- With the literal source definition of `epsilon2`, the equation-(2.28)
residual automatically satisfies the pointwise premise consumed by the
equation-(2.31) P-stage. -/
theorem cmp116Eq228PResidualWeight_le_eq231Pointwise
    {ιP : Type*}
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q blockScale : ℕ)
    (C2 kappa1 delta kappa unionMetric : ℝ)
    (gamma2 gapEpsilon1 gk epsilon2 : ℝ) (pBonds : Finset ιP)
    (hcoeff :
      0 ≤
        cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1)
    (hkappa : 0 ≤ kappa) (hfourDelta : 4 * delta ≤ 1)
    (hmetric : 0 ≤ unionMetric)
    (hepsilon2 :
      epsilon2 =
        cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1) :
    cmp116Eq228PResidualWeight
        E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
        delta kappa unionMetric gamma2 gapEpsilon1 gk pBonds ≤
      (2 * (((blockScale : ℝ) + 2) ^ 4) * epsilon2) *
        cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds := by
  have hresidual :
      cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa unionMetric ≤
        cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 :=
    cmp116Eq228Residual_le_sourceCoefficient
      E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
      delta kappa unionMetric hcoeff hkappa hfourDelta hmetric
  have hscale : 1 ≤ 2 * (((blockScale : ℝ) + 2) ^ 4) := by
    have hb : 0 ≤ (blockScale : ℝ) := by positivity
    have hsquare : 4 ≤ ((blockScale : ℝ) + 2) ^ 2 := by
      nlinarith [sq_nonneg (blockScale : ℝ)]
    have hfourth : 1 ≤ ((blockScale : ℝ) + 2) ^ 4 := by
      nlinarith [sq_nonneg ((((blockScale : ℝ) + 2) ^ 2) - 1)]
    nlinarith
  have hcoeffScale :
      cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 ≤
        2 * (((blockScale : ℝ) + 2) ^ 4) *
          cmp116Eq228SourceCoefficient
            E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale) hcoeff]
  unfold cmp116Eq228PResidualWeight
  rw [hepsilon2]
  calc
    cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa unionMetric *
        cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds ≤
      cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 *
        cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds := by
      exact mul_le_mul_of_nonneg_right hresidual
        (by
          unfold cmp116Eq226PBondFactor
          positivity)
    _ ≤
      (2 * (((blockScale : ℝ) + 2) ^ 4) *
          cmp116Eq228SourceCoefficient
            E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1) *
        cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds := by
      exact mul_le_mul_of_nonneg_right hcoeffScale
        (by
          unfold cmp116Eq226PBondFactor
          positivity)

end

end YangMills.RG
