/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq220ResidualLedger

/-!
# Equation (2.20) residual ledger with distinct inner and outer carriers

The residual domains are supported in `Z₀`, while the conditioned outer
Gaussian and the final polymer volume are carried by `Z`.  Under `Z₀ ⊆ Z`,
this module transports the rooted residual estimate to the literal outer
carrier without changing any domain or gap factor.
-/

namespace YangMills.RG

noncomputable section

/-- Mixed-carrier form of the equation-(2.26) residual ledger.  The explicit
nonnegativity of `rootBound` is needed only for outer sites not lying in
`Z₀`; it is not an operator or decay estimate. -/
theorem
    cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_conditionedResidualLedger_outerCard
    {Y I PIndex : Type*}
    [DecidableEq Y] [DecidableEq I] [DecidableEq PIndex]
    (D : Finset Y) (P : Finset PIndex) (Z0 Z : Finset I)
    (hZ0Z : Z0 ⊆ Z)
    (support : Y → Finset I)
    (domainDist : Y → ℝ) (domainMetric : Y → ℕ)
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa gamma2 gk threshold : ℝ}
    {L gapCard : ℕ}
    {rootBound baseRate outerCost Calpha5 alpha5 outerBound : ℝ}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hgk : gk ≠ 0) (hthreshold : threshold = epsilon1 / gk)
    (houter :
      outerBound ≤ Real.exp (outerCost * (Z.card : ℝ)))
    (hne : ∀ y ∈ D, (support y).Nonempty)
    (hsub : ∀ y ∈ D, support y ⊆ Z0)
    (hrootNonneg : 0 ≤ rootBound)
    (hroot : ∀ i ∈ Z0,
      ∑ y ∈ D.filter (fun y => i ∈ support y),
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) ≤ rootBound)
    (hbudget :
      rootBound + (baseRate + outerCost) ≤ Calpha5 * alpha5) :
    ((outerBound *
          Real.exp
            ((∑ y ∈ D,
              cmp116Eq220ResidualDomainWeight alpha4 delta kappa
                (domainDist y)) -
              gamma2 / 2 * threshold ^ 2 * (P.card : ℝ)) *
          Real.exp (baseRate * (Z.card : ℝ))) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric D) *
        cmp116Eq226GapFactor kappa1 L M gapCard ≤
      cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma2 gk L gapCard
        Calpha5 alpha5 Z.card domainMetric D P := by
  have hsubZ : ∀ y ∈ D, support y ⊆ Z := by
    intro y hy
    exact fun i hi => hZ0Z (hsub y hy hi)
  have hrootZ : ∀ i ∈ Z,
      ∑ y ∈ D.filter (fun y => i ∈ support y),
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) ≤ rootBound := by
    intro i hiZ
    by_cases hi0 : i ∈ Z0
    · exact hroot i hi0
    · have hfilter :
          D.filter (fun y => i ∈ support y) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro y hyD hisupport
        exact hi0 (hsub y hyD hisupport)
      rw [hfilter]
      simpa using hrootNonneg
  exact
    cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_residualLedger_outerCard
      D P Z support domainDist domainMetric
      hE0 hepsilon1 hC1 halpha4 hgk hthreshold houter
      hne hsubZ hrootZ hbudget

end

end YangMills.RG
