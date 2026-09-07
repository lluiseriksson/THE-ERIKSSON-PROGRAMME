/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214FiniteGaussianResidualStages
import YangMills.RG.BalabanCMP116Eq214CauchyProductRate
import YangMills.RG.BalabanCMP116Eq143To219
import YangMills.RG.BalabanCMP116Eq237

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

/-- The individual domain factor in (2.26) is exactly twice the inverse
contour radius printed in equation (2.18). -/
theorem cmp116Eq226DomainFactor_eq_two_mul_tauInverse
    {ιY : Type*}
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (domainMetric : ιY → ℕ) (Y : ιY) :
    cmp116Eq226DomainFactor E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa domainMetric Y =
      2 * cmp116Eq218TauInverse E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainMetric Y : ℝ) := by
  unfold cmp116Eq226DomainFactor cmp116Eq218TauInverse
  ring

/-- Multiplication by the solved source radius cancels the inverse-radius
part of the domain factor, leaving exactly the printed factor `2`. -/
theorem cmp116Eq218TauAbsSolved_mul_eq226DomainFactor
    {ιY : Type*}
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    {domainMetric : ιY → ℕ} {Y : ιY}
    (hE0 : E0 ≠ 0) (hepsilon1 : epsilon1 ≠ 0)
    (hC1 : C1 ≠ 0) (halpha4 : alpha4 ≠ 0) (hM : M ≠ 0) :
    cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa (domainMetric Y : ℝ) *
        cmp116Eq226DomainFactor E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric Y = 2 := by
  rw [cmp116Eq226DomainFactor_eq_two_mul_tauInverse]
  rw [← cmp116Eq218_tauAbsSolved_inv_eq_tauInverse
    hE0 hepsilon1 hC1 halpha4 hM]
  have htau :
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainMetric Y : ℝ) ≠ 0 := by
    unfold cmp116Eq218TauAbsSolved
    positivity
  field_simp

/-- Product version of the source-radius cancellation over a fixed domain
family `D`.  This is the exact finite product consumed by the inner Cauchy
family once its coordinates are enumerated by `D`. -/
theorem cmp116Eq218TauRadiusProduct_mul_eq226DomainProduct
    {ιY : Type*} [DecidableEq ιY]
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    {domainMetric : ιY → ℕ} (D : Finset ιY)
    (hE0 : E0 ≠ 0) (hepsilon1 : epsilon1 ≠ 0)
    (hC1 : C1 ≠ 0) (halpha4 : alpha4 ≠ 0) (hM : M ≠ 0) :
    (∏ Y ∈ D,
        cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa (domainMetric Y : ℝ)) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric D =
      2 ^ D.card := by
  unfold cmp116Eq226DomainProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_pow_card
  intro Y hY
  exact cmp116Eq218TauAbsSolved_mul_eq226DomainFactor
    hE0 hepsilon1 hC1 halpha4 hM

/-- For the source radii from (2.18), the exact inner Cauchy loss is bounded
by multiplication with the domain product printed in (2.26).  The spare
factor is precisely `2 ^ |D|`; no radius comparison is assumed. -/
theorem cmp116Eq214CauchyRate_le_mul_eq226DomainProduct
    {n : ℕ}
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    {domainMetric : Fin n → ℕ} {boundaryMajorant : ℝ}
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (hboundary : 0 ≤ boundaryMajorant) :
    cmp116Eq214CauchyRate n
        (fun Y => cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa (domainMetric Y : ℝ))
        boundaryMajorant ≤
      boundaryMajorant *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric Finset.univ := by
  let radius : Fin n → ℝ := fun Y =>
    cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa (domainMetric Y : ℝ)
  have hradius : ∀ Y, 0 < radius Y := by
    intro Y
    dsimp [radius, cmp116Eq218TauAbsSolved]
    positivity
  have hradiusProd : 0 < ∏ Y, radius Y := by
    exact Finset.prod_pos fun Y _ => hradius Y
  have hM0 : M ≠ 0 := by omega
  have hcancel :
      (∏ Y, radius Y) *
          cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa domainMetric Finset.univ =
        (2 : ℝ) ^ n := by
    simpa [radius] using
      (cmp116Eq218TauRadiusProduct_mul_eq226DomainProduct
        (D := (Finset.univ : Finset (Fin n)))
        hE0.ne' hepsilon1.ne' hC1.ne' halpha4.ne' hM0)
  rw [cmp116Eq214CauchyRate_eq_div_prod]
  apply (div_le_iff₀ hradiusProd).2
  calc
    boundaryMajorant ≤ boundaryMajorant * (2 : ℝ) ^ n := by
      simpa using
        (mul_le_mul_of_nonneg_left
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) :
            (1 : ℝ) ≤ (2 : ℝ) ^ n) hboundary)
    _ = boundaryMajorant *
          cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa domainMetric Finset.univ *
          ∏ Y, radius Y := by
      rw [← hcancel]
      ring

/-- A literal equation-(2.14) term whose inner contour radii are those of
(2.18) loses at most the domain product of (2.26).  The outer `sigma` Cauchy
family remains visible for the subsequent `P`/gap analysis. -/
theorem CMP116Eq214AnalyticData.norm_term_le_deltaCauchyRate_mul_eq226DomainProduct
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond) (psi : Ψ) (phi : Φ)
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    (domainMetric : Fin nY → ℕ) (boundaryMajorant : ℝ)
    (hDelta : ∀ i, 0 < A.deltaRadius i)
    (hYRadius : A.yRadius = fun Y =>
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainMetric Y : ℝ))
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (hboundaryMajorant : 0 ≤ boundaryMajorant)
    (hbound : CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      A.deltaRadius A.yRadius
      (fun sigma tau => A.analyticIntegrand Y0 P sigma tau psi phi)
      boundaryMajorant) :
    ‖A.term Y0 P psi phi‖ ≤
      cmp116Eq214CauchyRate nDelta A.deltaRadius
        (boundaryMajorant *
          cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa domainMetric Finset.univ) := by
  have hY : ∀ i, 0 < A.yRadius i := by
    intro i
    rw [hYRadius]
    unfold cmp116Eq218TauAbsSolved
    positivity
  have hterm := A.norm_term_le_cauchyRate Y0 P psi phi boundaryMajorant
    hDelta hY hbound
  refine hterm.trans ?_
  apply cmp116Eq214CauchyRate_mono nDelta A.deltaRadius _ _ hDelta
  rw [hYRadius]
  exact cmp116Eq214CauchyRate_le_mul_eq226DomainProduct
    hE0 hepsilon1 hC1 halpha4 hM hboundaryMajorant

/-- The `P`-bond factor
`exp (-1/2 * gamma2 * epsilon1^2 / gk^2 * |P|)` from (2.26). -/
def cmp116Eq226PBondFactor
    {ιP : Type*}
    (gamma2 epsilon1 gk : ℝ) (P : Finset ιP) : ℝ :=
  Real.exp
    (-((1 / 2 : ℝ) * gamma2 * epsilon1 ^ 2 * (gk ^ 2)⁻¹ *
      (P.card : ℝ)))

/-- Once the physical threshold is `epsilon1 / gk`, the negative cardinality
factor retained by equation (2.22) is literally the `P` factor printed in
equation (2.26). -/
theorem cmp116Eq222PenaltyFactor_eq_eq226PBondFactor
    {ιP : Type*}
    (gamma2 epsilon1 gk threshold : ℝ) (P : Finset ιP)
    (hgk : gk ≠ 0) (hthreshold : threshold = epsilon1 / gk) :
    Real.exp (-(gamma2 / 2 * threshold ^ 2 * (P.card : ℝ))) =
      cmp116Eq226PBondFactor gamma2 epsilon1 gk P := by
  rw [hthreshold]
  unfold cmp116Eq226PBondFactor
  congr 1
  field_simp [hgk]

/-- Residual-cost version used directly by the physical boundary theorem. -/
theorem cmp116Eq222ResidualPenaltyFactor_eq_mul_eq226PBondFactor
    {ιP : Type*}
    (gamma2 epsilon1 gk threshold residual : ℝ) (P : Finset ιP)
    (hgk : gk ≠ 0) (hthreshold : threshold = epsilon1 / gk) :
    Real.exp
        (residual - gamma2 / 2 * threshold ^ 2 * (P.card : ℝ)) =
      Real.exp residual * cmp116Eq226PBondFactor gamma2 epsilon1 gk P := by
  rw [sub_eq_add_neg, Real.exp_add,
    cmp116Eq222PenaltyFactor_eq_eq226PBondFactor
      gamma2 epsilon1 gk threshold P hgk hthreshold]

/-- The rate isolated for the equation-(2.31) P-bond resummation. -/
def cmp116Eq226PSourceRate
    (gamma2 epsilon1 gk : ℝ) : ℝ :=
  gamma2 * epsilon1 ^ 2 / (20 * gk ^ 2)

/-- The P penalty in (2.26) contains ten units of the source rate used in
equation (2.31). -/
theorem cmp116Eq226PBondFactor_eq_exp_ten_mul_sourceRate
    {ιP : Type*}
    (gamma2 epsilon1 gk : ℝ) (P : Finset ιP) :
    cmp116Eq226PBondFactor gamma2 epsilon1 gk P =
      Real.exp (-(10 * cmp116Eq226PSourceRate gamma2 epsilon1 gk *
        (P.card : ℝ))) := by
  unfold cmp116Eq226PBondFactor cmp116Eq226PSourceRate
  congr 1
  ring

/-- Equivalently, the P penalty supplies five copies of the cardinality
factor `exp (-2 * rate * |P|)` appearing inside the equation-(2.31) weight.
This identity records the exact source reserve before any entropy estimate. -/
theorem cmp116Eq226PBondFactor_eq_eq231CardinalityFactor_pow_five
    {ιP : Type*}
    (gamma2 epsilon1 gk : ℝ) (P : Finset ιP) :
    cmp116Eq226PBondFactor gamma2 epsilon1 gk P =
      (Real.exp (-(2 * cmp116Eq226PSourceRate gamma2 epsilon1 gk *
        (P.card : ℝ)))) ^ 5 := by
  rw [cmp116Eq226PBondFactor_eq_exp_ten_mul_sourceRate]
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- Cross-dictionary monotonicity for the literal `P` factor.  The premise is
the exact comparison of the source and target cardinality penalties, so it
also applies when the two finite bond types differ. -/
theorem cmp116Eq226PBondFactor_le_of_penalty
    {ιP ιP' : Type*}
    (sourceGamma sourceEpsilon sourceGk : ℝ) (sourceP : Finset ιP)
    (targetGamma targetEpsilon targetGk : ℝ) (targetP : Finset ιP')
    (hpenalty :
      targetGamma * targetEpsilon ^ 2 * (targetGk ^ 2)⁻¹ *
          (targetP.card : ℝ) ≤
        sourceGamma * sourceEpsilon ^ 2 * (sourceGk ^ 2)⁻¹ *
          (sourceP.card : ℝ)) :
    cmp116Eq226PBondFactor
        sourceGamma sourceEpsilon sourceGk sourceP ≤
      cmp116Eq226PBondFactor
        targetGamma targetEpsilon targetGk targetP := by
  unfold cmp116Eq226PBondFactor
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The gap factor
`exp (-(kappa1-1) * (L*M)^(-4) * |Z \ Z0'|)` from (2.26). -/
def cmp116Eq226GapFactor
    (kappa1 : ℝ) (L M gapCard : ℕ) : ℝ :=
  Real.exp
    (-((kappa1 - 1) * (((L * M : ℕ) : ℝ) ^ 4)⁻¹ *
      (gapCard : ℝ)))

/-- Cross-dictionary monotonicity for the gap factor, expressed directly in
terms of the two normalized gap penalties. -/
theorem cmp116Eq226GapFactor_le_of_penalty
    (sourceKappa1 : ℝ) (sourceL sourceM sourceGapCard : ℕ)
    (targetKappa1 : ℝ) (targetL targetM targetGapCard : ℕ)
    (hpenalty :
      (targetKappa1 - 1) *
          ((((targetL * targetM : ℕ) : ℝ) ^ 4)⁻¹) *
          (targetGapCard : ℝ) ≤
        (sourceKappa1 - 1) *
          ((((sourceL * sourceM : ℕ) : ℝ) ^ 4)⁻¹) *
          (sourceGapCard : ℝ)) :
    cmp116Eq226GapFactor
        sourceKappa1 sourceL sourceM sourceGapCard ≤
      cmp116Eq226GapFactor
        targetKappa1 targetL targetM targetGapCard := by
  unfold cmp116Eq226GapFactor
  exact Real.exp_le_exp.mpr (neg_le_neg hpenalty)

/-- The final Gaussian volume factor `exp (C_alpha5 * alpha5 * |Z|)`. -/
def cmp116Eq226GaussianVolumeFactor
    (Calpha5 alpha5 : ℝ) (sourceCard : ℕ) : ℝ :=
  Real.exp (Calpha5 * alpha5 * (sourceCard : ℝ))

/-- Cross-dictionary monotonicity for the Gaussian volume factor. -/
theorem cmp116Eq226GaussianVolumeFactor_le_of_exponent
    (sourceCalpha5 sourceAlpha5 : ℝ) (sourceCard : ℕ)
    (targetCalpha5 targetAlpha5 : ℝ) (targetCard : ℕ)
    (hexponent :
      sourceCalpha5 * sourceAlpha5 * (sourceCard : ℝ) ≤
        targetCalpha5 * targetAlpha5 * (targetCard : ℝ)) :
    cmp116Eq226GaussianVolumeFactor
        sourceCalpha5 sourceAlpha5 sourceCard ≤
      cmp116Eq226GaussianVolumeFactor
        targetCalpha5 targetAlpha5 targetCard := by
  unfold cmp116Eq226GaussianVolumeFactor
  exact Real.exp_le_exp.mpr hexponent

/-- The fixed-`Z0'` weight of equation (2.37) is the gap and Gaussian-volume
part of (2.26), with the later connected-component product left explicitly
between them. -/
theorem cmp116Eq237FixedZ0PrimeWeight_eq_eq226Factors
    {σ ιZ0' ιC : Type*}
    (hp : CMP116Lemma3Parameters)
    (L M : ℕ) (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (Z : σ) (Z0' : ιZ0') :
    cmp116Eq237FixedZ0PrimeWeight hp (L * M) C237 Calpha5 alpha5
        sourceCard gapCard components componentMetric Z Z0' =
      cmp116Eq226GapFactor hp.kappa1 L M (gapCard Z Z0') *
        (Finset.prod (components Z Z0') (fun Zi =>
          cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2 *
            Real.exp
              (-(((1 - 7 * hp.delta) / 2) *
                (hp.blockScale : ℝ) * hp.kappa *
                  (componentMetric Z Z0' Zi : ℝ))))) *
        cmp116Eq226GaussianVolumeFactor Calpha5 alpha5 (sourceCard Z) := by
  unfold cmp116Eq237FixedZ0PrimeWeight cmp116Eq226GapFactor
    cmp116Eq226GaussianVolumeFactor
  norm_num

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

/-- Factorwise source dictionary for the literal equation-(2.26) ledger.
This theorem performs only the monotone algebra: the four comparison
premises retain the exact domain, `P`, gap, and Gaussian-volume obligations
that must be proved by the physical dictionaries. -/
theorem cmp116Eq226SourceTermWeight_le_targetLedger_of_factorwise
    {ιY ιP : Type*}
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa gamma2 gk : ℝ)
    (L gapCard : ℕ)
    (Calpha5 alpha5 : ℝ) (sourceCard : ℕ)
    (domainMetric : ιY → ℕ) (D : Finset ιY) (P : Finset ιP)
    (targetDomain targetP targetGap targetGaussian : ℝ)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hdomain :
      cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric D ≤
        targetDomain)
    (hP :
      cmp116Eq226PBondFactor gamma2 epsilon1 gk P ≤
        targetP)
    (hgap :
      cmp116Eq226GapFactor kappa1 L M gapCard ≤
        targetGap)
    (hgaussian :
      cmp116Eq226GaussianVolumeFactor Calpha5 alpha5 sourceCard ≤
        targetGaussian) :
    cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma2 gk L gapCard
        Calpha5 alpha5 sourceCard domainMetric D P ≤
      targetDomain * targetP * targetGap * targetGaussian := by
  have hsourceDomain :
      0 ≤
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric D := by
    unfold cmp116Eq226DomainProduct
    exact
      Finset.prod_nonneg fun Y _hY =>
        cmp116Eq226DomainFactor_nonneg hE0 hepsilon1 hC1 halpha4
  have hsourceP :
      0 ≤ cmp116Eq226PBondFactor gamma2 epsilon1 gk P :=
    Real.exp_nonneg _
  have hsourceGap :
      0 ≤ cmp116Eq226GapFactor kappa1 L M gapCard :=
    Real.exp_nonneg _
  have hsourceGaussian :
      0 ≤
        cmp116Eq226GaussianVolumeFactor Calpha5 alpha5 sourceCard :=
    Real.exp_nonneg _
  have htargetDomain : 0 ≤ targetDomain :=
    hsourceDomain.trans hdomain
  have htargetP : 0 ≤ targetP :=
    hsourceP.trans hP
  have htargetGap : 0 ≤ targetGap :=
    hsourceGap.trans hgap
  have htargetGaussian : 0 ≤ targetGaussian :=
    hsourceGaussian.trans hgaussian
  unfold cmp116Eq226SourceTermWeight
  calc
    cmp116Eq226GapFactor kappa1 L M gapCard *
          cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa domainMetric D *
        cmp116Eq226PBondFactor gamma2 epsilon1 gk P *
      cmp116Eq226GaussianVolumeFactor Calpha5 alpha5 sourceCard ≤
        targetGap * targetDomain * targetP * targetGaussian := by
      gcongr
    _ = targetDomain * targetP * targetGap * targetGaussian := by
      ring

/-- Source dictionary expressed only by the domain-product comparison and
the three scalar exponent/cardinality comparisons. -/
theorem cmp116Eq226SourceTermWeight_le_targetLedger_of_scalarDictionaries
    {ιY ιP ιP' : Type*}
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa gamma2 gk : ℝ)
    (L gapCard : ℕ)
    (Calpha5 alpha5 : ℝ) (sourceCard : ℕ)
    (domainMetric : ιY → ℕ) (D : Finset ιY) (P : Finset ιP)
    (targetDomain : ℝ)
    (targetGamma targetEpsilon targetGk : ℝ)
    (targetP : Finset ιP')
    (targetKappa1 : ℝ)
    (targetL targetM targetGapCard : ℕ)
    (targetCalpha5 targetAlpha5 : ℝ) (targetCard : ℕ)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hdomain :
      cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric D ≤
        targetDomain)
    (hPpenalty :
      targetGamma * targetEpsilon ^ 2 * (targetGk ^ 2)⁻¹ *
          (targetP.card : ℝ) ≤
        gamma2 * epsilon1 ^ 2 * (gk ^ 2)⁻¹ * (P.card : ℝ))
    (hgappenalty :
      (targetKappa1 - 1) *
          ((((targetL * targetM : ℕ) : ℝ) ^ 4)⁻¹) *
          (targetGapCard : ℝ) ≤
        (kappa1 - 1) *
          ((((L * M : ℕ) : ℝ) ^ 4)⁻¹) *
          (gapCard : ℝ))
    (hgaussianExponent :
      Calpha5 * alpha5 * (sourceCard : ℝ) ≤
        targetCalpha5 * targetAlpha5 * (targetCard : ℝ)) :
    cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma2 gk L gapCard
        Calpha5 alpha5 sourceCard domainMetric D P ≤
      targetDomain *
        cmp116Eq226PBondFactor
          targetGamma targetEpsilon targetGk targetP *
        cmp116Eq226GapFactor
          targetKappa1 targetL targetM targetGapCard *
        cmp116Eq226GaussianVolumeFactor
          targetCalpha5 targetAlpha5 targetCard := by
  exact
    cmp116Eq226SourceTermWeight_le_targetLedger_of_factorwise
      E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa gamma2 gk
      L gapCard Calpha5 alpha5 sourceCard domainMetric D P
      targetDomain
      (cmp116Eq226PBondFactor
        targetGamma targetEpsilon targetGk targetP)
      (cmp116Eq226GapFactor
        targetKappa1 targetL targetM targetGapCard)
      (cmp116Eq226GaussianVolumeFactor
        targetCalpha5 targetAlpha5 targetCard)
      hE0 hepsilon1 hC1 halpha4 hdomain
      (cmp116Eq226PBondFactor_le_of_penalty
        gamma2 epsilon1 gk P
        targetGamma targetEpsilon targetGk targetP hPpenalty)
      (cmp116Eq226GapFactor_le_of_penalty
        kappa1 L M gapCard
        targetKappa1 targetL targetM targetGapCard hgappenalty)
      (cmp116Eq226GaussianVolumeFactor_le_of_exponent
        Calpha5 alpha5 sourceCard
        targetCalpha5 targetAlpha5 targetCard hgaussianExponent)

end

end YangMills.RG
