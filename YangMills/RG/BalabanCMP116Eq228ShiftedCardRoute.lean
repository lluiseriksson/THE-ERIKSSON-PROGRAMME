/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq228PResidualWeight
import YangMills.RG.BalabanCMP116Eq229CubeTreeMetric

/-!
# Convention-robust source route for CMP116 equation (2.28)

The physical source-tree metric satisfies the convention-independent lower
comparison

`|Y| / 24 ≤ d_k(Y) + 1`.

Consequently the shifted cardinal metric is pointwise below `d_k`.  It also
satisfies equation (2.27) on every nonempty exact-union fiber.  This gives a
fully constructed equation-(2.28) extraction while retaining the actual
source-tree metric in the equation-(2.29) product.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- The shifted equation-(2.30) comparison puts the canonical shifted
cardinal metric below any physical metric. -/
theorem cmp116Eq229ShiftedCardMetric_le_of_eq230Shifted
    {V : Type*}
    (metric : Finset V → ℕ) (Y : Finset V)
    (hEq230Shifted :
      (Y.card : ℝ) / 24 ≤ (metric Y : ℝ) + 1) :
    cmp116Eq229ShiftedCardMetric Y ≤ metric Y := by
  have hceil :
      cmp116Eq229CardMetric Y ≤ metric Y + 1 := by
    apply
      (ceilDiv_le_iff_le_mul
        (a := 24) (b := Y.card) (c := metric Y + 1)
        (by norm_num)).mpr
    have hreal :
        (Y.card : ℝ) ≤ 24 * ((metric Y : ℝ) + 1) := by
      nlinarith
    exact_mod_cast hreal
  calc
    cmp116Eq229ShiftedCardMetric Y =
        (cmp116Eq229CardMetric Y).pred := rfl
    _ ≤ (metric Y + 1).pred := Nat.pred_le_pred hceil
    _ = metric Y := by simp

/-- Exact-union equation-(2.28) producer using the shifted cardinal lower
metric.  Equation (2.27) and nonemptiness of the selected domain family are
derived internally. -/
theorem cmp116Eq226DomainProduct_le_eq229Product_mul_eq228Residual_shiftedCard
    {V : Type*} [DecidableEq V]
    (domainFamily : Finset (Finset V))
    (Y0 : Finset V) (hY0 : Y0.Nonempty)
    (hdomains : ∀ Y ∈ domainFamily, Y.Nonempty)
    (D : Finset (Finset V))
    (hD : D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0)
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (domainMetric : Finset V → ℕ)
    (hEq230Shifted :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (domainMetric Y : ℝ) + 1)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 < alpha4)
    (halpha6 : 0 < alpha6)
    (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa)
    (hfourDelta : 4 * delta ≤ 1)
    (hsmall :
      cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 *
        Real.exp (5 * kappa) ≤ 1) :
    cmp116Eq226DomainProduct
        E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
        domainMetric D ≤
      (∏ Y ∈ D,
          cmp116Eq229Weight alpha6 delta kappa domainMetric Y) *
        cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa
          (cmp116Eq229ShiftedCardMetric Y0 : ℝ) := by
  have hsource :=
    (mem_cmp116Eq229ExactUnionDIndex_iff domainFamily Y0 D).mp hD
  have hDnonempty : D.Nonempty := by
    by_contra hDempty
    rw [Finset.not_nonempty_iff_eq_empty] at hDempty
    subst D
    have : Y0 = ∅ := by
      simpa [cmp116Eq23Y0] using hsource.2.symm
    exact hY0.ne_empty this
  have hlower :
      ∀ Y ∈ D,
        cmp116Eq229ShiftedCardMetric Y ≤ domainMetric Y := by
    intro Y hYD
    exact
      cmp116Eq229ShiftedCardMetric_le_of_eq230Shifted
        domainMetric Y (hEq230Shifted Y (hsource.1 hYD))
  have hEq227 :
      (cmp116Eq229ShiftedCardMetric Y0 : ℝ) + 5 ≤
        ∑ Y ∈ D,
          ((cmp116Eq229ShiftedCardMetric Y : ℝ) + 5) :=
    cmp116Eq229ShiftedCardMetric_eq227
      domainFamily hdomains Y0 hY0 D hD
  exact
    cmp116Eq226DomainProduct_le_eq229Product_mul_eq228Residual_of_lowerMetric
      D hDnonempty E0 epsilon1 C1 alpha4 alpha6 M q
      C2 kappa1 delta kappa
      domainMetric cmp116Eq229ShiftedCardMetric
      (cmp116Eq229ShiftedCardMetric Y0 : ℝ)
      hE0 hepsilon1 hC1 halpha4 halpha6
      hdelta hkappa hfourDelta hsmall hlower hEq227

/-- Fully physical cube-source-tree specialization of equation (2.28). -/
theorem cmp116Eq226DomainProduct_le_eq229Product_mul_eq228Residual_cubeSourceTree
    {L : ℕ} [NeZero L]
    (domainFamily : Finset (Finset (Cube 4 L)))
    (Y0 : Finset (Cube 4 L)) (hY0 : Y0.Nonempty)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧ walkConnected (cmp116CubeFaceAdj L) Y)
    (D : Finset (Finset (Cube 4 L)))
    (hD : D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0)
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 < alpha4)
    (halpha6 : 0 < alpha6)
    (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa)
    (hfourDelta : 4 * delta ≤ 1)
    (hsmall :
      cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 *
        Real.exp (5 * kappa) ≤ 1) :
    cmp116Eq226DomainProduct
        E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
        cmp116CubeSourceTreeMetric D ≤
      (∏ Y ∈ D,
          cmp116Eq229Weight
            alpha6 delta kappa cmp116CubeSourceTreeMetric Y) *
        cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa
          (cmp116Eq229ShiftedCardMetric Y0 : ℝ) := by
  exact
    cmp116Eq226DomainProduct_le_eq229Product_mul_eq228Residual_shiftedCard
      domainFamily Y0 hY0 (fun Y hY => (hdomains Y hY).1)
      D hD E0 epsilon1 C1 alpha4 alpha6 M q
      C2 kappa1 delta kappa cmp116CubeSourceTreeMetric
      (fun Y hY =>
        cmp116CubeSourceTreeMetric_eq230_shifted
          Y (hdomains Y hY).1 (hdomains Y hY).2)
      hE0 hepsilon1 hC1 halpha4 halpha6
      hdelta hkappa hfourDelta hsmall

/-- Physical equation-(2.26) domain-plus-bond ledger reduced to the actual
equation-(2.29) product and the literal post-domain P residual. -/
theorem cmp116Eq226DomainProduct_mul_PBondFactor_le_eq229Product_mul_eq228PResidual_cubeSourceTree
    {L : ℕ} [NeZero L] {ιP : Type*}
    (domainFamily : Finset (Finset (Cube 4 L)))
    (Y0 : Finset (Cube 4 L)) (hY0 : Y0.Nonempty)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧ walkConnected (cmp116CubeFaceAdj L) Y)
    (D : Finset (Finset (Cube 4 L)))
    (hD : D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0)
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (gamma2 gapEpsilon1 gk : ℝ) (pBonds : Finset ιP)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 < alpha4)
    (halpha6 : 0 < alpha6)
    (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa)
    (hfourDelta : 4 * delta ≤ 1)
    (hsmall :
      cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 *
        Real.exp (5 * kappa) ≤ 1) :
    cmp116Eq226DomainProduct
          E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
          cmp116CubeSourceTreeMetric D *
        cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds ≤
      (∏ Y ∈ D,
          cmp116Eq229Weight
            alpha6 delta kappa cmp116CubeSourceTreeMetric Y) *
        cmp116Eq228PResidualWeight
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa
          (cmp116Eq229ShiftedCardMetric Y0 : ℝ)
          gamma2 gapEpsilon1 gk pBonds := by
  have hdomain :=
    cmp116Eq226DomainProduct_le_eq229Product_mul_eq228Residual_cubeSourceTree
      domainFamily Y0 hY0 hdomains D hD
      E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 delta kappa
      hE0 hepsilon1 hC1 halpha4 halpha6
      hdelta hkappa hfourDelta hsmall
  calc
    cmp116Eq226DomainProduct
          E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
          cmp116CubeSourceTreeMetric D *
        cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds ≤
      ((∏ Y ∈ D,
          cmp116Eq229Weight
            alpha6 delta kappa cmp116CubeSourceTreeMetric Y) *
        cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa
          (cmp116Eq229ShiftedCardMetric Y0 : ℝ)) *
        cmp116Eq226PBondFactor gamma2 gapEpsilon1 gk pBonds := by
      exact mul_le_mul_of_nonneg_right hdomain
        (by
          unfold cmp116Eq226PBondFactor
          positivity)
    _ =
      (∏ Y ∈ D,
          cmp116Eq229Weight
            alpha6 delta kappa cmp116CubeSourceTreeMetric Y) *
        cmp116Eq228PResidualWeight
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa
          (cmp116Eq229ShiftedCardMetric Y0 : ℝ)
          gamma2 gapEpsilon1 gk pBonds := by
      unfold cmp116Eq228PResidualWeight
      ring

end

end YangMills.RG
