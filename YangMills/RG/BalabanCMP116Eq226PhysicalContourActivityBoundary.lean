/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalContourCutoffSupportResidualLedger
import YangMills.RG.BalabanCMP116Eq214LocalActivityIdentification
import YangMills.RG.BalabanCMP116Lemma3ScaleFamily
import YangMills.RG.BalabanCMP116Eq221OperatorForms

/-!
# Literal equation-(2.26) terms as a Lemma-3 activity boundary

This module connects the literal complex-contour estimate to the existing
Lemma-3 resummation machinery.  A source record below retains the physical
inputs of the contour theorem: the actual density, Cauchy radii, localized
Gaussian bounds, cutoff inequality, source energy, rooted residual ledger,
and scalar volume budget.  It does not store a termwise estimate.

From a family of these records, the resummation term weight is definitionally
the printed equation-(2.26) weight, while the activity is definitionally the
finite sum of the corresponding local equation-(2.14) activities.  Hence both
fields of `CMP116Lemma3ActivityTermwiseScaleBoundary` are derived.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

/-- Source data and genuine physical obligations for one literal
equation-(2.14) term.  No norm bound on the complete term is stored here. -/
structure CMP116Eq226PhysicalContourTermSource
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E : Type*} [Norm E]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℝ) (q : ℕ)
    (C2 kappa1 delta kappa gamma gk : ℝ)
    (alpha outerBound outerRate sourceRate : ℝ)
    (Y0 P : Finset (Cube d L)) (Z0 : Finset (FinBox d N')) where
  contour :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) (PhysicalBond d (M * N'))
      (fun _ => SUNLieCoord Nc) (fun _ => SUNLieCoord Nc) E lieDim
  source :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ
  domainMetric : Fin nY → ℕ
  domainSupport : Fin nY → Finset (FinBox d N')
  gapScale : ℕ
  gapCard : ℕ
  rootBound : ℝ
  volumeRate : ℝ
  outerCost : ℝ
  deltaRadius_eq :
    contour.deltaRadius = fun _ => cmp116Eq214SigmaCauchyRadius kappa1
  normalizedGap :
    ((((gapScale * M : ℕ) : ℝ) ^ 4)⁻¹ * (gapCard : ℝ)) =
      (nDelta : ℝ)
  yRadius_eq :
    contour.yRadius = fun Y =>
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainMetric Y : ℝ)
  E0_pos : 0 < E0
  epsilon1_pos : 0 < epsilon1
  C1_pos : 0 < C1
  alpha4_pos : 0 < alpha4
  one_le_M : 1 ≤ M
  gk_ne : gk ≠ 0
  threshold_eq : contour.threshold = epsilon1 / gk
  alpha_nonneg : 0 ≤ alpha
  covariance_small : alpha * ‖contour.referenceRoot‖ ^ 2 < 1
  sourceRate_nonneg : 0 ≤ sourceRate
  outerRate_nonneg : 0 ≤ outerRate
  gaussian_small :
    2 * (outerRate +
      cmp116Eq225SourceCoefficient contour.referenceRoot alpha *
        sourceRate) < 1
  outerBound_nonneg : 0 ≤ outerBound
  outerBound_le_exp_card :
    outerBound ≤ Real.exp (outerCost * (Z0.card : ℝ))
  gamma_nonneg : 0 ≤ gamma
  threshold_nonneg : 0 ≤ contour.threshold
  outer_bound :
    ∀ psi phi sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta contour.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY contour.yRadius tau →
      ∀ x,
        ‖contour.toLocalFiniteGaussianData.toFiniteGaussianData.outerWeight
            sigma tau psi phi x‖ ≤
          outerBound *
            Real.exp (outerRate *
              ∑ i ∈ Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0,
                x i ^ 2)
  inner_bound :
    ∀ psi phi sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta contour.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY contour.yRadius tau →
      ∀ x b,
        ‖contour.toLocalFiniteGaussianData.toFiniteGaussianData.innerWeight
            sigma tau psi phi x b‖ ≤
          Real.exp (∑ i, source sigma tau x i * b i)
  potentialRate : ℝ
  r2Rate : ℝ
  potentialRate_nonneg : 0 ≤ potentialRate
  potential_bound :
    ∀ psi phi sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta contour.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY contour.yRadius tau →
      ∀ b,
        contour.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.cutoffFactor
            Y0 P b ≠ 0 →
        (contour.potential sigma tau psi phi b).re ≤
          potentialRate / 2 *
            (b ⬝ᵥ
              Matrix.mulVec
                (cmp116Eq223CoordinateProjection
                  (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)) b) +
          ∑ Y : Fin nY,
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainMetric Y : ℝ)
  r2_bound :
    ∀ psi phi sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta contour.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY contour.yRadius tau →
      ∀ b,
        contour.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.cutoffFactor
            Y0 P b ≠ 0 →
        (cmp116Eq214ComplexQuadratic
            (contour.r2Matrix sigma tau psi phi) b).re ≤
          r2Rate / 2 *
            (b ⬝ᵥ
              Matrix.mulVec
                (cmp116Eq223CoordinateProjection
                  (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)) b)
  cutoff_energy_bound :
    ∀ b,
      (∑ e ∈ P,
          ‖contour.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
            b e‖ ^ 2) ≤
        b ⬝ᵥ
          Matrix.mulVec
            (cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)) b
  interaction_budget : potentialRate + r2Rate + gamma ≤ alpha
  source_bound :
    ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta contour.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY contour.yRadius tau →
      ∀ x,
        (source sigma tau x) ⬝ᵥ (source sigma tau x) ≤
          sourceRate *
            (∑ i ∈ Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0,
              x i ^ 2) + 0
  domain_nonempty : ∀ Y : Fin nY, (domainSupport Y).Nonempty
  domain_subset : ∀ Y : Fin nY, domainSupport Y ⊆ Z0
  rooted_residual :
    ∀ i ∈ Z0,
      ∑ Y ∈ (Finset.univ.filter fun Y : Fin nY =>
          i ∈ domainSupport Y),
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa
          (domainMetric Y : ℝ) ≤ rootBound
  volume_budget :
    rootBound +
        (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
            M d Nc contour.referenceRoot alpha
              (outerRate +
                cmp116Eq225SourceCoefficient contour.referenceRoot alpha *
                  sourceRate) +
          outerCost) ≤
      volumeRate * alpha

namespace CMP116Eq226PhysicalContourTermSource

variable
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E : Type*} [Norm E]
    {Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim}
    {E0 epsilon1 C1 alpha4 : ℝ} {q : ℕ}
    {C2 kappa1 delta kappa gamma gk : ℝ}
    {alpha outerBound outerRate sourceRate : ℝ}
    {Y0 P : Finset (Cube d L)} {Z0 : Finset (FinBox d N')}

/-- The literal equation-(2.26) weight attached to a source term. -/
def termWeight
    (S : CMP116Eq226PhysicalContourTermSource
      (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
      (Nc := Nc) (L := L) (lieDim := lieDim) (E := E) Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate Y0 P Z0) : ℝ :=
  cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
    C2 kappa1 delta kappa gamma gk S.gapScale S.gapCard
    S.volumeRate alpha Z0.card S.domainMetric Finset.univ P

/-- The four source-facing component bounds reproduce the former literal
`interaction_bound` contract exactly.  This theorem is intentionally public:
future changes to the source record must continue to imply this same
cutoff-supported inequality. -/
theorem interaction_bound
    (S : CMP116Eq226PhysicalContourTermSource
      (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
      (Nc := Nc) (L := L) (lieDim := lieDim) (E := E) Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate Y0 P Z0)
    (psi phi : PhysicalGaugeField d (M * N') Nc) :
    ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta S.contour.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY S.contour.yRadius tau →
      ∀ b,
        S.contour.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.cutoffFactor
            Y0 P b ≠ 0 →
        (S.contour.toLocalFiniteGaussianData.toFiniteGaussianData.interactionExponent
            sigma tau psi phi b).re +
          (gamma / 2) *
            (∑ e ∈ P,
              ‖S.contour.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
                b e‖ ^ 2) ≤
        -((b ⬝ᵥ
          Matrix.mulVec
            (-(alpha • cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0))) b) /
            2) +
          ∑ Y : Fin nY,
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (S.domainMetric Y : ℝ) := by
  intro sigma tau hsigma htau b hcutoff
  let localizedCoordinates :=
    Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0
  let energyB :=
    b ⬝ᵥ
      Matrix.mulVec
        (cmp116Eq223CoordinateProjection localizedCoordinates) b
  let energyP :=
    ∑ e ∈ P,
      ‖S.contour.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
        b e‖ ^ 2
  let residual :=
    ∑ Y : Fin nY,
      cmp116Eq220ResidualDomainWeight alpha4 delta kappa
        (S.domainMetric Y : ℝ)
  let localPsi :=
    restrictGlobal S.contour.spectatorSupport psi
  let localPhi :=
    restrictGlobal S.contour.fluctuationSupport phi
  have henergyB : 0 ≤ energyB := by
    exact
      (cmp116Eq223CoordinateProjection_posSemidef localizedCoordinates)
        |>.dotProduct_mulVec_nonneg b
  have hcombined :=
    cmp116Eq220_eq221_eq222_absorb_into_alpha5
      (potentialTerm :=
        (S.contour.potential sigma tau localPsi localPhi b).re)
      (operatorTerm :=
        (cmp116Eq214ComplexQuadratic
          (S.contour.r2Matrix sigma tau localPsi localPhi) b).re)
      (potentialRate := S.potentialRate)
      (operatorRate := S.r2Rate)
      (cutoff := gamma)
      (alpha5 := alpha)
      (energyP := energyP)
      (energyX := 0)
      (energyB := energyB)
      (residual20 := residual)
      (residual21 := 0)
      (S.potential_bound localPsi localPhi sigma tau hsigma htau b hcutoff)
      (by
        simpa [energyB] using
          S.r2_bound localPsi localPhi sigma tau hsigma htau b hcutoff)
      (by simpa [energyP, energyB] using S.cutoff_energy_bound b)
      S.potentialRate_nonneg S.gamma_nonneg (by norm_num) henergyB
      S.interaction_budget
  change
    (cmp116Eq214ComplexQuadratic
          (S.contour.r2Matrix sigma tau localPsi localPhi) b).re +
        (S.contour.potential sigma tau localPsi localPhi b).re +
          gamma / 2 * energyP ≤
      -((b ⬝ᵥ Matrix.mulVec
        (-(alpha • cmp116Eq223CoordinateProjection localizedCoordinates)) b) /
          2) + residual
  have hmatrix :
      -((b ⬝ᵥ Matrix.mulVec
        (-(alpha • cmp116Eq223CoordinateProjection localizedCoordinates)) b) /
          2) =
        alpha / 2 * energyB := by
    rw [show
      -(alpha • cmp116Eq223CoordinateProjection localizedCoordinates) =
        (-alpha) • cmp116Eq223CoordinateProjection localizedCoordinates by
          simp]
    rw [Matrix.smul_mulVec, dotProduct_smul]
    simp [energyB, smul_eq_mul]
    ring
  rw [hmatrix]
  linarith

/-- The source record produces the termwise estimate; it does not assume it. -/
theorem norm_term_le_termWeight
    (S : CMP116Eq226PhysicalContourTermSource
      (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
      (Nc := Nc) (L := L) (lieDim := lieDim) (E := E) Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate Y0 P Z0)
    (psi phi : PhysicalGaugeField d (M * N') Nc) :
    ‖S.contour.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.term
        Y0 P psi phi‖ ≤
      S.termWeight := by
  exact
    S.contour.norm_term_le_eq226SourceTermWeight_of_outerInteractionEnergy_cutoffSupport_residualLedger
      Dict Y0 P Z0 psi phi
      alpha outerBound S.outerCost outerRate sourceRate gamma S.source
      S.domainMetric S.domainSupport S.gapScale S.gapCard
      S.rootBound S.volumeRate S.deltaRadius_eq S.normalizedGap
      S.yRadius_eq S.E0_pos S.epsilon1_pos S.C1_pos S.alpha4_pos
      S.one_le_M S.gk_ne S.threshold_eq S.alpha_nonneg
      S.covariance_small S.sourceRate_nonneg S.outerRate_nonneg
      S.gaussian_small S.outerBound_nonneg S.outerBound_le_exp_card
      S.gamma_nonneg S.threshold_nonneg
      (S.outer_bound psi phi) (S.inner_bound psi phi)
      (S.interaction_bound psi phi) S.source_bound
      S.domain_nonempty S.domain_subset S.rooted_residual S.volume_budget

end CMP116Eq226PhysicalContourTermSource

universe uE uZ uS

/-- A source record for every member of one dependent `D/P/Z0/Z0'` stack. -/
def CMP116Eq226PhysicalContourTermSourceFamily
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E : Type uE} {ιZ0' : Type uZ} [Norm E]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℝ) (q : ℕ)
    (C2 kappa1 delta kappa gamma gk : ℝ)
    (alpha outerBound outerRate sourceRate : ℝ)
    (σ : Type uS) : Type (max uE uZ uS) :=
  ∀ (_Z : σ) (D P : Finset (Cube d L))
      (Z0 : Finset (FinBox d N')) (_Z0p : ιZ0'),
    CMP116Eq226PhysicalContourTermSource
      (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
      (Nc := Nc) (L := L) (lieDim := lieDim) (E := E) Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate D P Z0

/-- The literal complex-contour resummation whose weight is definitionally
the printed equation-(2.26) source weight. -/
def cmp116Eq226PhysicalContourResummation
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E ιZ0' σ : Type*} [Norm E] [DecidableEq ιZ0']
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℝ) (q : ℕ)
    (C2 kappa1 delta kappa gamma gk : ℝ)
    (alpha outerBound outerRate sourceRate : ℝ)
    (DIndex : σ → Finset (Finset (Cube d L)))
    (PIndex :
      σ → Finset (Cube d L) → Finset (Finset (Cube d L)))
    (Z0Index :
      σ → Finset (Cube d L) → Finset (Cube d L) →
        Finset (Finset (FinBox d N')))
    (Z0PrimeIndex :
      σ → Finset (Cube d L) → Finset (Cube d L) →
        Finset (FinBox d N') → Finset ιZ0')
    (S : CMP116Eq226PhysicalContourTermSourceFamily
      (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
      (Nc := Nc) (L := L) (lieDim := lieDim) (E := E) (ιZ0' := ιZ0')
      Dict E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate σ) :
    CMP116HResummation σ
      (Finset (Cube d L)) (Finset (Cube d L))
      (Finset (FinBox d N')) ιZ0'
      (PhysicalGaugeField d (M * N') Nc)
      (PhysicalGaugeField d (M * N') Nc) where
  DIndex := DIndex
  PIndex := PIndex
  Z0Index := Z0Index
  Z0PrimeIndex := Z0PrimeIndex
  summand := fun Z D P Z0 Z0p psi phi =>
    (S Z D P Z0 Z0p).contour.toLocalFiniteGaussianData.toFiniteGaussianData
      |>.toAnalyticData.term D P psi phi
  termWeight := fun Z D P Z0 Z0p =>
    (S Z D P Z0 Z0p).termWeight

/-- The physical local activity assembled before global evaluation. -/
def cmp116Eq226PhysicalContourActivity
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E ιZ0' σ : Type*} [Norm E]
    [DecidableEq ιZ0']
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℝ) (q : ℕ)
    (C2 kappa1 delta kappa gamma gk : ℝ)
    (alpha outerBound outerRate sourceRate : ℝ)
    (DIndex : σ → Finset (Finset (Cube d L)))
    (PIndex :
      σ → Finset (Cube d L) → Finset (Finset (Cube d L)))
    (Z0Index :
      σ → Finset (Cube d L) → Finset (Cube d L) →
        Finset (Finset (FinBox d N')))
    (Z0PrimeIndex :
      σ → Finset (Cube d L) → Finset (Cube d L) →
        Finset (FinBox d N') → Finset ιZ0')
    (S : CMP116Eq226PhysicalContourTermSourceFamily
      (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
      (Nc := Nc) (L := L) (lieDim := lieDim) (E := E) (ιZ0' := ιZ0')
      Dict E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate σ)
    (Z : σ) :
    PhysicalGaugeLocalActivity d (M * N') Nc :=
  let R := cmp116Eq226PhysicalContourResummation Dict
    E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
    alpha outerBound outerRate sourceRate
    DIndex PIndex Z0Index Z0PrimeIndex S
  LocalActivity.finsetSum (cmp116HIndexFinset R Z) fun x =>
    (S Z x.1.1 x.1.2 x.2.1 x.2.2).contour.toLocalFiniteGaussianData
      |>.toLocalAnalyticData.localTerm x.1.1 x.1.2

/-- Global evaluation of the assembled physical local activity is exactly the
literal complex-contour resummation. -/
@[simp] theorem globalEval_cmp116Eq226PhysicalContourActivity
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E ιZ0' σ : Type*} [Norm E] [DecidableEq ιZ0']
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℝ) (q : ℕ)
    (C2 kappa1 delta kappa gamma gk : ℝ)
    (alpha outerBound outerRate sourceRate : ℝ)
    (DIndex : σ → Finset (Finset (Cube d L)))
    (PIndex :
      σ → Finset (Cube d L) → Finset (Finset (Cube d L)))
    (Z0Index :
      σ → Finset (Cube d L) → Finset (Cube d L) →
        Finset (Finset (FinBox d N')))
    (Z0PrimeIndex :
      σ → Finset (Cube d L) → Finset (Cube d L) →
        Finset (FinBox d N') → Finset ιZ0')
    (S : CMP116Eq226PhysicalContourTermSourceFamily
      (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
      (Nc := Nc) (L := L) (lieDim := lieDim) (E := E) (ιZ0' := ιZ0')
      Dict E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate σ)
    (Z : σ) (psi phi : PhysicalGaugeField d (M * N') Nc) :
    (cmp116Eq226PhysicalContourActivity Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
        DIndex PIndex Z0Index Z0PrimeIndex S Z).globalEval psi phi =
      balabanCMP116H
        (cmp116Eq226PhysicalContourResummation Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S) Z psi phi := by
  rw [cmp116Eq226PhysicalContourActivity, LocalActivity.globalEval_finsetSum]
  rfl

/-- Every term of the source-indexed resummation satisfies its definitionally
installed equation-(2.26) weight. -/
theorem cmp116Eq226PhysicalContourResummation_termwise
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E ιZ0' σ : Type*} [Norm E] [DecidableEq ιZ0']
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℝ) (q : ℕ)
    (C2 kappa1 delta kappa gamma gk : ℝ)
    (alpha outerBound outerRate sourceRate : ℝ)
    (DIndex : σ → Finset (Finset (Cube d L)))
    (PIndex :
      σ → Finset (Cube d L) → Finset (Finset (Cube d L)))
    (Z0Index :
      σ → Finset (Cube d L) → Finset (Cube d L) →
        Finset (Finset (FinBox d N')))
    (Z0PrimeIndex :
      σ → Finset (Cube d L) → Finset (Cube d L) →
        Finset (FinBox d N') → Finset ιZ0')
    (S : CMP116Eq226PhysicalContourTermSourceFamily
      (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
      (Nc := Nc) (L := L) (lieDim := lieDim) (E := E) (ιZ0' := ιZ0')
      Dict E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate σ) :
    let R := cmp116Eq226PhysicalContourResummation Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S
    ∀ Z x, x ∈ cmp116HIndexFinset R Z →
      ∀ psi phi,
        ‖R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 psi phi‖ ≤
          R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2 := by
  dsimp
  intro Z x _ psi phi
  exact
    (S Z x.1.1 x.1.2 x.2.1 x.2.2).norm_term_le_termWeight psi phi

/-- The literal complex-contour resummation at every RG scale. -/
def cmp116Eq226PhysicalContourResummationScaleFamily
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E : Type*} [Norm E]
    {σ ιZ0' : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιZ0' _t _k)]
    (Dict : ∀ _t _k,
      PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℕ → ℕ → ℝ)
    (q : ℕ → ℕ → ℕ)
    (C2 kappa1 delta kappa gamma gk : ℕ → ℕ → ℝ)
    (alpha outerBound outerRate sourceRate : ℕ → ℕ → ℝ)
    (DIndex :
      ∀ t k, σ t k → Finset (Finset (Cube d L)))
    (PIndex :
      ∀ t k, σ t k → Finset (Cube d L) →
        Finset (Finset (Cube d L)))
    (Z0Index :
      ∀ t k, σ t k → Finset (Cube d L) → Finset (Cube d L) →
        Finset (Finset (FinBox d N')))
    (Z0PrimeIndex :
      ∀ t k, σ t k → Finset (Cube d L) → Finset (Cube d L) →
        Finset (FinBox d N') → Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
        (Nc := Nc) (L := L) (lieDim := lieDim) (E := E)
        (ιZ0' := ιZ0' t k)
        (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
        (gamma t k) (gk t k) (alpha t k) (outerBound t k)
        (outerRate t k) (sourceRate t k) (σ t k)) :
    ∀ t k,
      CMP116HResummation (σ t k)
        (Finset (Cube d L)) (Finset (Cube d L))
        (Finset (FinBox d N')) (ιZ0' t k)
        (PhysicalGaugeField d (M * N') Nc)
        (PhysicalGaugeField d (M * N') Nc) :=
  fun t k =>
    cmp116Eq226PhysicalContourResummation (Dict t k)
      (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k) (q t k)
      (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
      (gamma t k) (gk t k) (alpha t k) (outerBound t k)
      (outerRate t k) (sourceRate t k)
      (DIndex t k) (PIndex t k) (Z0Index t k) (Z0PrimeIndex t k) (S t k)

/-- The finite sum of local physical contour terms at every RG scale. -/
def cmp116Eq226PhysicalContourActivityScaleFamily
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E : Type*} [Norm E]
    {σ ιZ0' : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιZ0' _t _k)]
    (Dict : ∀ _t _k,
      PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℕ → ℕ → ℝ)
    (q : ℕ → ℕ → ℕ)
    (C2 kappa1 delta kappa gamma gk : ℕ → ℕ → ℝ)
    (alpha outerBound outerRate sourceRate : ℕ → ℕ → ℝ)
    (DIndex :
      ∀ t k, σ t k → Finset (Finset (Cube d L)))
    (PIndex :
      ∀ t k, σ t k → Finset (Cube d L) →
        Finset (Finset (Cube d L)))
    (Z0Index :
      ∀ t k, σ t k → Finset (Cube d L) → Finset (Cube d L) →
        Finset (Finset (FinBox d N')))
    (Z0PrimeIndex :
      ∀ t k, σ t k → Finset (Cube d L) → Finset (Cube d L) →
        Finset (FinBox d N') → Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
        (Nc := Nc) (L := L) (lieDim := lieDim) (E := E)
        (ιZ0' := ιZ0' t k)
        (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
        (gamma t k) (gk t k) (alpha t k) (outerBound t k)
        (outerRate t k) (sourceRate t k) (σ t k)) :
    ∀ t k, σ t k → PhysicalGaugeLocalActivity d (M * N') Nc :=
  fun t k =>
    cmp116Eq226PhysicalContourActivity (Dict t k)
      (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k) (q t k)
      (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
      (gamma t k) (gk t k) (alpha t k) (outerBound t k)
      (outerRate t k) (sourceRate t k)
      (DIndex t k) (PIndex t k) (Z0Index t k) (Z0PrimeIndex t k) (S t k)

/-- Source-faithful scale boundary: activity identification and the termwise
equation-(2.26) estimate are both generated from literal contour records. -/
theorem cmp116Eq226PhysicalContour_activityTermwiseScaleBoundary
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E : Type*} [Norm E]
    {σ ιZ0' : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιZ0' _t _k)]
    (Dict : ∀ _t _k,
      PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℕ → ℕ → ℝ)
    (q : ℕ → ℕ → ℕ)
    (C2 kappa1 delta kappa gamma gk : ℕ → ℕ → ℝ)
    (alpha outerBound outerRate sourceRate : ℕ → ℕ → ℝ)
    (DIndex :
      ∀ t k, σ t k → Finset (Finset (Cube d L)))
    (PIndex :
      ∀ t k, σ t k → Finset (Cube d L) →
        Finset (Finset (Cube d L)))
    (Z0Index :
      ∀ t k, σ t k → Finset (Cube d L) → Finset (Cube d L) →
        Finset (Finset (FinBox d N')))
    (Z0PrimeIndex :
      ∀ t k, σ t k → Finset (Cube d L) → Finset (Cube d L) →
        Finset (FinBox d N') → Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
        (Nc := Nc) (L := L) (lieDim := lieDim) (E := E)
        (ιZ0' := ιZ0' t k)
        (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
        (gamma t k) (gk t k) (alpha t k) (outerBound t k)
        (outerRate t k) (sourceRate t k) (σ t k)) :
    CMP116Lemma3ActivityTermwiseScaleBoundary
      (cmp116Eq226PhysicalContourResummationScaleFamily Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
        DIndex PIndex Z0Index Z0PrimeIndex S)
      (cmp116Eq226PhysicalContourActivityScaleFamily Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
        DIndex PIndex Z0Index Z0PrimeIndex S) where
  activity_identification := by
    intro t k Z psi phi
    exact globalEval_cmp116Eq226PhysicalContourActivity
      (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
      (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
      (gamma t k) (gk t k) (alpha t k) (outerBound t k)
      (outerRate t k) (sourceRate t k)
      (DIndex t k) (PIndex t k) (Z0Index t k) (Z0PrimeIndex t k)
      (S t k) Z psi phi
  termwise_estimate := by
    intro t k
    exact cmp116Eq226PhysicalContourResummation_termwise
      (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
      (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
      (gamma t k) (gk t k) (alpha t k) (outerBound t k)
      (outerRate t k) (sourceRate t k)
      (DIndex t k) (PIndex t k) (Z0Index t k) (Z0PrimeIndex t k)
      (S t k)

/-- Consume the literal contour boundary with the existing source-shaped
Eq. (2.29), `P`, and post-`P` stages.  The caller no longer supplies either
activity identification or a termwise estimate. -/
def cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_boundaries
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E : Type*} [Norm E]
    {σ ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιZ0' _t _k)]
    (Dict : ∀ _t _k,
      PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℕ → ℕ → ℝ)
    (q : ℕ → ℕ → ℕ)
    (C2 kappa1 delta kappa gamma gk : ℕ → ℕ → ℝ)
    (alpha outerBound outerRate sourceRate : ℕ → ℕ → ℝ)
    (DIndex :
      ∀ t k, σ t k → Finset (Finset (Cube d L)))
    (PIndex :
      ∀ t k, σ t k → Finset (Cube d L) →
        Finset (Finset (Cube d L)))
    (Z0Index :
      ∀ t k, σ t k → Finset (Cube d L) → Finset (Cube d L) →
        Finset (Finset (FinBox d N')))
    (Z0PrimeIndex :
      ∀ t k, σ t k → Finset (Cube d L) → Finset (Cube d L) →
        Finset (FinBox d N') → Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
        (Nc := Nc) (L := L) (lieDim := lieDim) (E := E)
        (ιZ0' := ιZ0' t k)
        (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
        (gamma t k) (gk t k) (alpha t k) (outerBound t k)
        (outerRate t k) (sourceRate t k) (σ t k))
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (DParts :
      ∀ t k, σ t k → Finset (Cube d L) → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, σ t k → Finset (Cube d L) → Finset (Cube d L) → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary hp
        (cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        (cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary hp
        (cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude) :
    CMP116Lemma3ActivityEstimateScaleFamily
      (cmp116Eq226PhysicalContourActivityScaleFamily Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
        DIndex PIndex Z0Index Z0PrimeIndex S)
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries
      eq229 pStage postP
      (cmp116Eq226PhysicalContour_activityTermwiseScaleBoundary Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
        DIndex PIndex Z0Index Z0PrimeIndex S)

end

end YangMills.RG
