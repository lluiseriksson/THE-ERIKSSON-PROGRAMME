/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214FiniteGaussianResidualStages

/-!
# The literal source ledger in CMP116 equation (2.26)

This module transcribes the four factors displayed in CMP116 (2.26): the
`Z \ Z0'` gap penalty, the product over localization domains `Y ∈ D`, the
large-field bond penalty indexed by `P`, and the Gaussian volume cost.  It
does not assume the estimate of the physical term by this ledger; that is the
remaining source-to-Lean analytic theorem.
-/

namespace YangMills.RG

noncomputable section

/-- The individual `Y ∈ D` factor printed in CMP116 (2.26). -/
def cmp116Eq226DomainFactor
    {ιY : Type*}
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (domainMetric : ιY → ℕ) (Y : ιY) : ℝ :=
  2 * E0 * epsilon1 * C1 * alpha4⁻¹ * (M : ℝ) ^ q *
    Real.exp (C2 * kappa1) *
    Real.exp (-((1 - 3 * delta) * kappa * (domainMetric Y : ℝ)))

/-- Product over all localization domains in the family `D`. -/
def cmp116Eq226DomainProduct
    {ιY : Type*}
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (domainMetric : ιY → ℕ) (D : Finset ιY) : ℝ :=
  Finset.prod D
    (cmp116Eq226DomainFactor E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa domainMetric)

/-- The `P`-bond factor
`exp (-1/2 * gamma2 * epsilon1^2 / gk^2 * |P|)` from (2.26). -/
def cmp116Eq226PBondFactor
    {ιP : Type*}
    (gamma2 epsilon1 gk : ℝ) (P : Finset ιP) : ℝ :=
  Real.exp
    (-((1 / 2 : ℝ) * gamma2 * epsilon1 ^ 2 * (gk ^ 2)⁻¹ *
      (P.card : ℝ)))

/-- The gap factor
`exp (-(kappa1-1) * (L*M)^(-4) * |Z \ Z0'|)` from (2.26). -/
def cmp116Eq226GapFactor
    (kappa1 : ℝ) (L M gapCard : ℕ) : ℝ :=
  Real.exp
    (-((kappa1 - 1) * (((L * M : ℕ) : ℝ) ^ 4)⁻¹ *
      (gapCard : ℝ)))

/-- The final Gaussian volume factor `exp (C_alpha5 * alpha5 * |Z|)`. -/
def cmp116Eq226GaussianVolumeFactor
    (Calpha5 alpha5 : ℝ) (sourceCard : ℕ) : ℝ :=
  Real.exp (Calpha5 * alpha5 * (sourceCard : ℝ))

/-- Literal right-hand side of CMP116 (2.26).  The arguments `gapCard` and
`sourceCard` stand respectively for `|Z \ Z0'|` and `|Z|`. -/
def cmp116Eq226SourceTermWeight
    {ιY ιP : Type*}
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa gamma2 gk : ℝ)
    (L gapCard : ℕ)
    (Calpha5 alpha5 : ℝ) (sourceCard : ℕ)
    (domainMetric : ιY → ℕ) (D : Finset ιY) (P : Finset ιP) : ℝ :=
  cmp116Eq226GapFactor kappa1 L M gapCard *
    cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa domainMetric D *
    cmp116Eq226PBondFactor gamma2 epsilon1 gk P *
    cmp116Eq226GaussianVolumeFactor Calpha5 alpha5 sourceCard

/-- Stage weights matching exactly the source summation order following
(2.26): `D`, then `P`, then the trivial `Z0` factor, then `Z0'`. -/
def cmp116Eq226DStageWeight
    {ιY : Type*}
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (domainMetric : ιY → ℕ) (D : Finset ιY) : ℝ :=
  cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
    C2 kappa1 delta kappa domainMetric D

def cmp116Eq226PStageWeight
    {ιP : Type*} (gamma2 epsilon1 gk : ℝ) (P : Finset ιP) : ℝ :=
  cmp116Eq226PBondFactor gamma2 epsilon1 gk P

def cmp116Eq226Z0StageWeight : ℝ := 1

def cmp116Eq226Z0PrimeStageWeight
    (kappa1 : ℝ) (L M gapCard : ℕ) : ℝ :=
  cmp116Eq226GapFactor kappa1 L M gapCard

def cmp116Eq226SourceStageWeight
    (Calpha5 alpha5 : ℝ) (sourceCard : ℕ) : ℝ :=
  cmp116Eq226GaussianVolumeFactor Calpha5 alpha5 sourceCard

/-- Exact factorization of the printed (2.26) bound into the already
formalized source stages. -/
theorem cmp116Eq226SourceTermWeight_eq_stageLedger
    {ιY ιP : Type*}
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa gamma2 gk : ℝ)
    (L gapCard : ℕ)
    (Calpha5 alpha5 : ℝ) (sourceCard : ℕ)
    (domainMetric : ιY → ℕ) (D : Finset ιY) (P : Finset ιP) :
    cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma2 gk L gapCard
        Calpha5 alpha5 sourceCard domainMetric D P =
      cmp116Eq226SourceStageWeight Calpha5 alpha5 sourceCard *
        cmp116Eq226DStageWeight E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric D *
        cmp116Eq226PStageWeight gamma2 epsilon1 gk P *
        cmp116Eq226Z0StageWeight *
        cmp116Eq226Z0PrimeStageWeight kappa1 L M gapCard := by
  unfold cmp116Eq226SourceTermWeight cmp116Eq226SourceStageWeight
    cmp116Eq226DStageWeight cmp116Eq226PStageWeight
    cmp116Eq226Z0StageWeight cmp116Eq226Z0PrimeStageWeight
  ring

theorem cmp116Eq226DomainFactor_nonneg
    {ιY : Type*}
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    {domainMetric : ιY → ℕ} {Y : ιY}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4) :
    0 ≤ cmp116Eq226DomainFactor E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa domainMetric Y := by
  unfold cmp116Eq226DomainFactor
  positivity

theorem cmp116Eq226SourceTermWeight_nonneg
    {ιY ιP : Type*}
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa gamma2 gk : ℝ}
    {L gapCard : ℕ}
    {Calpha5 alpha5 : ℝ} {sourceCard : ℕ}
    {domainMetric : ιY → ℕ} {D : Finset ιY} {P : Finset ιP}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4) :
    0 ≤ cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa gamma2 gk L gapCard
      Calpha5 alpha5 sourceCard domainMetric D P := by
  unfold cmp116Eq226SourceTermWeight
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Real.exp_nonneg _)
        (Finset.prod_nonneg fun Y _ =>
          cmp116Eq226DomainFactor_nonneg hE0 hepsilon1 hC1 halpha4))
      (Real.exp_nonneg _))
    (Real.exp_nonneg _)

end

end YangMills.RG
