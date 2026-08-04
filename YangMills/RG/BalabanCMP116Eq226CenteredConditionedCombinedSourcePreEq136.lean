/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226CenteredConditionedCombinedPartialTermSourceConstructor
import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedRootedResidual
import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedVolumeBudget
import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedTerminalEq143
import YangMills.RG.BalabanCMP116InteractingPhysicalPrecisionSource

/-!
# Source-specific pre-(1.36) assembly on the combined ledger

PRE-VALIDATION: the conditioned covariance, root and lower certificate are
now generated from the physical precision source, but this refactor has not
yet been materialized or checked by the compiler.

The preceding 17/41 assembler was compiler-verified at source checkpoint
`7fb235a3c86d3077b3d978a24a5623cd562eef9c`.  The interacting-precision
installation in this revision was compiler-verified from one fresh Colab
CPU/high-RAM clone at source checkpoint
`5b061eb968885f5d724dc3b9226ee593ddc5d0db`.

This module removes the circular `S : PreEq136` input from the combined
constructor.  Raw physical data are separated from proof inputs, while the
literal direct/native total, residual, domain dictionary, kernel support,
amplitude, cutoff threshold, optimal interaction coefficient, rooted bound,
and volume rate are definitions.  The proof record is therefore unable to
carry any of those generated objects under a renamed field.

The final assembler below is intentionally source-facing: it retains the
parametrix, contour, covariance, jet, and scalar windows which are not yet
derived from the Wilson action.  It does not manufacture a `TermSource` and
does not discharge equation (1.36).
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev CombinedSourceBond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

private abbrev CombinedSourceFineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CombinedSourceCoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev CombinedSourceRectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CombinedSourceCoarseField Q Nc →L[ℝ]
    CombinedSourceFineField M Q Nc

private abbrev CombinedSourceEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Raw data for the literal direct/native pre-source.  None of the fields
is a completed `PreEq136`, a terminal estimate, or a generated dictionary.
The choice and Lemma-1 certificate are pinned to the preceding source
parameters in their field types. -/
structure CMP116CenteredConditionedCombinedSourceData
    {Index : Type*} {nDelta M Q Nc n L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (P : Finset (CombinedSourceBond M Q))
    (Z : Finset (FinBox 4 (2 * Q)))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (baseCoarseCovariance :
      CombinedSourceCoarseField Q Nc →L[ℝ]
        CombinedSourceCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (D D₃ : CombinedSourceFineField M Q Nc →
      CombinedSourceCoarseField Q Nc)
    (V₀ : CombinedSourceFineField M Q Nc → ℝ)
    (Pprop T : CombinedSourceRectangularFieldMap M Q Nc)
    (DeltaPi : CombinedSourceFineField M Q Nc →L[ℝ]
      CombinedSourceFineField M Q Nc)
    (J : CombinedSourceFineField M Q Nc) where
  base :
    CMP116Eq214PhysicalContourDensity nDelta
      (CMP116Eq80Lemma1CombinedDomainCount anchor domains E)
      (CombinedSourceBond M Q) (CombinedSourceBond M Q)
      (fun _ => SUNLieCoord Nc) (fun _ => SUNLieCoord Nc)
      (SUNLieCoord Nc) (Nc ^ 2 - 1)
  contourCarrier : Finset (FinBox 4 (2 * Q))
  contourEquiv : Fin nDelta ≃ ↑contourCarrier
  precisionSource : CMP116InteractingPhysicalPrecisionSource V
  localizedCarrier_nonempty :
    (cmp116SourcePhysicalLocalizedCoordinates Dict
      (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P)).Nonempty
  choice : CMP99SourcePi4CoarseFineWalkChoice M Q (3 * M) layerWord
  mass : ℝ
  mass_pos : 0 < mass
  Ahead : ℝ
  rho : ℝ
  rate : ℝ
  radius : ℝ
  Delta : ℕ
  E0Direct : ℝ
  epsilon1 : ℝ
  C1 : ℝ
  alpha4 : ℝ
  C3 : ℝ
  C2 : ℝ
  kappa1 : ℝ
  delta : ℝ
  kappa : ℝ
  gk : ℝ
  rowSum : ℝ
  gamma : ℝ
  q : ℕ
  gapScale : ℕ
  gapCard : ℕ
  qBound : ℝ
  lemma1 : CMP109Lemma1Eq136SourceCertificate (q := q)
    E V gk D epsilon1 C1 C2 kappa1 delta kappa
  C : ℝ
  Rjet : ℝ
  sourceJetBound : ℝ
  cardRatio : ℝ
  metricRatio : ℝ
  summationRatio : ℝ
  kappaCard : ℝ

namespace CMP116CenteredConditionedCombinedSourceData

variable
    {Index : Type*} {nDelta M Q Nc n L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] [NeZero L] [NeZero lieDim]
    {Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim}
    {P : Finset (CombinedSourceBond M Q)}
    {Z : Finset (FinBox 4 (2 * Q))}
    {anchor : FinBox 4 Q}
    {domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor)}
    {E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc}
    {V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc}
    {baseCoarseCovariance :
      CombinedSourceCoarseField Q Nc →L[ℝ]
        CombinedSourceCoarseField Q Nc}
    {layerWord : Fin n → ℕ}
    {D D₃ : CombinedSourceFineField M Q Nc →
      CombinedSourceCoarseField Q Nc}
    {V₀ : CombinedSourceFineField M Q Nc → ℝ}
    {Pprop T : CombinedSourceRectangularFieldMap M Q Nc}
    {DeltaPi : CombinedSourceFineField M Q Nc →L[ℝ]
      CombinedSourceFineField M Q Nc}
    {J : CombinedSourceFineField M Q Nc}

/-- Literal localized coordinate carrier of the combined direct/native
source. -/
noncomputable def localizedCoordinates
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :=
  cmp116SourcePhysicalLocalizedCoordinates Dict
    (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P)

/-- The combined raw region packaged in the proof-carrying index used by the
terminal centered-conditioned family. -/
noncomputable def localizedRegion
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    CMP116SourcePhysicalLocalizedRegion Dict :=
  ⟨cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P,
    X.localizedCarrier_nonempty⟩

@[simp] theorem localizedRegion_val
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    X.localizedRegion.1 =
      cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P := rfl

/-- The literal combined localized coordinate carrier is nonempty.  This is
the exact geometric datum required by the conditioned covariance: unlike a
`P.Nonempty` field, it also covers valid terms with `P = ∅` whose witness
comes from the direct branch of the combined region. -/
theorem localizedCoordinates_nonempty
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    X.localizedCoordinates.Nonempty := by
  exact X.localizedRegion.2

/-- Literal compression of the inverse interacting precision to the combined
localized carrier. -/
noncomputable def conditionedCovariance
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :=
  X.precisionSource.conditionedCovariance X.localizedCoordinates

/-- Positive localized square root reconstructed as the physical terminal
root.  It is no longer an independent datum of the source record. -/
noncomputable def root
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    CombinedSourceEndomorphism M Q Nc :=
  X.precisionSource.conditionedRoot X.localizedCoordinates

/-- Exact square-root/support certificate generated from the physical
interacting precision. -/
def conditionedRoot
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    MatrixConditionedGaussianRootCertificate
      X.conditionedCovariance
      (cmp116PhysicalEndomorphismRealMatrix X.root)
      X.localizedCoordinates := by
  exact X.precisionSource.conditionedRoot_certificate X.localizedCoordinates

/-- Strict localized covariance lower certificate.  Its carrier witness is
the geometric producer above and its analytic bound is generated internally
from coercivity and the precision norm. -/
def conditionedCovariance_nondegenerate
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    MatrixConditionedGaussianCovarianceLowerCertificate
      X.conditionedCovariance X.localizedCoordinates := by
  exact X.precisionSource.conditionedCovariance_lowerCertificate
    X.localizedCoordinates X.localizedCoordinates_nonempty

/-- Literal interacting Wilson-plus-gauge precision installed in the source. -/
noncomputable def K
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    CombinedSourceEndomorphism M Q Nc :=
  X.precisionSource.precision

/-- Exact finite range of the literal interacting precision. -/
def sourceRange
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℕ :=
  X.precisionSource.sourceRange

/-- Surviving physical coercivity of the literal interacting precision. -/
def coercivityConstant
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℝ :=
  X.precisionSource.coercivityConstant

theorem sourceRange_bound
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J)
    (hM : 1 ≤ M) :
    X.sourceRange + 1 ≤ 4 * M :=
  X.precisionSource.sourceRange_bound hM

theorem finiteRange
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    PhysicalCovarianceFiniteRange X.K physicalBondDist X.sourceRange :=
  X.precisionSource.finiteRange

theorem coercivity_pos
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    0 < X.coercivityConstant :=
  X.precisionSource.coercivity_pos

theorem K_coercive
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    IsCoerciveCLM X.K X.coercivityConstant :=
  X.precisionSource.coercive

/-- Exact interacting covariance paired with `K`; it is kept distinct from
the conditioned Gaussian root used by the terminal contour measure. -/
noncomputable def interactingCovariance
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    CombinedSourceEndomorphism M Q Nc :=
  X.precisionSource.covariance

theorem K_comp_interactingCovariance
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :
    X.K.comp X.interactingCovariance =
      ContinuousLinearMap.id ℝ (CombinedSourceFineField M Q Nc) :=
  X.precisionSource.precision_comp_covariance

/-- Literal direct/native total installed by the source assembler. -/
noncomputable def total
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :=
  cmp116CenteredConditionedCombinedEq80PartialTotal
    (nDelta := nDelta)
    X.base.spectatorSupport X.base.fluctuationSupport anchor domains E V
    X.contourCarrier X.contourEquiv X.K (by exact X.coercivity_pos)
    (by exact X.mass_pos) (by exact X.K_coercive) baseCoarseCovariance
    layerWord X.choice D D₃ V₀ Pprop T DeltaPi J X.gk

/-- Literal direct/native residual installed by the source assembler. -/
noncomputable def residual
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) :=
  cmp116CenteredConditionedCombinedEq80PartialResidual
    (nDelta := nDelta)
    X.base.spectatorSupport X.base.fluctuationSupport anchor domains E V
    X.contourCarrier X.contourEquiv X.K (by exact X.coercivity_pos)
    (by exact X.mass_pos) (by exact X.K_coercive) baseCoarseCovariance
    layerWord X.choice D D₃ V₀ Pprop T DeltaPi J X.gk

/-- Canonical combined amplitude; positivity comes from the positive native
certificate and the nonnegative direct amplitude. -/
def E0
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℝ :=
  X.E0Direct + X.lemma1.E0

/-- Literal source cutoff threshold. -/
def threshold
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℝ :=
  X.epsilon1 / X.gk

/-- Canonical common rooted bound on the appended direct/native ledger. -/
noncomputable def rootBound
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℝ :=
  cmp116Eq80Lemma1CombinedPhysicalRootBound
    X.E0 X.epsilon1 X.C1 M X.q X.C2 X.kappa1 X.delta X.kappa X.alpha4

/-- The literal potential rate entering the optimal interaction coefficient. -/
noncomputable def potentialRate
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℝ :=
  cmp116Eq220CenteredSourcePotentialRate Finset.univ
    (fun y => (cmp116Eq80Lemma1CombinedDomainMetric anchor domains E y : ℝ))
    (cmp116Eq80Lemma1CombinedDomainCard anchor domains E)
    X.C3 X.epsilon1 M X.C2 X.kappa1 X.alpha4 X.rowSum

/-- The literal bilateral complex-quadratic rate. -/
noncomputable def r2Rate
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℝ :=
  cmp116SourcePi4PhysicalComplexR2BilateralBound
    X.K X.Delta X.Ahead X.rho X.rate X.radius (1 + X.radius)

/-- Minimal interaction coefficient permitted by the three quadratic rates. -/
noncomputable def alpha
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℝ :=
  cmp116Eq226OptimalInteractionAlpha X.potentialRate X.r2Rate X.gamma

/-- Literal source-energy rate entering the outer Gaussian cost. -/
noncomputable def sourceRate
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℝ :=
  cmp116SourcePi4PhysicalComplexR3SourceRate X.K X.root
    (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P)
    X.Delta X.Ahead X.rho X.rate X.radius (1 + X.radius)

/-- Literal determinant cost of the restricted contour. -/
noncomputable def determinantCost
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℝ :=
  cmp116SourceRestrictedUniformContourDeterminantCost
    M Nc X.Delta X.radius (1 + X.radius) X.rate X.Ahead X.rho
      ‖cmp116PhysicalEndomorphismComplexMatrix X.K‖

/-- Canonical least volume coefficient.  Its positivity denominator remains
an explicit scalar input to the proof record. -/
noncomputable def volumeRate
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) : ℝ :=
  cmp116Eq80Lemma1CombinedPhysicalVolumeRate (q := X.q)
    X.K X.root X.coercivity_pos X.mass_pos X.K_coercive
    (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P)
    X.Delta X.radius X.rate X.Ahead X.rho X.alpha X.sourceRate X.qBound
    X.determinantCost X.E0 X.epsilon1 X.C1 X.C2 X.kappa1 X.delta
    X.kappa X.alpha4

end CMP116CenteredConditionedCombinedSourceData

/-- The obligations which still have to be supplied after the literal
combined data have been fixed.  In particular this record has no fields for
`total`, `residual`, any domain dictionary, `kernelSupport`, `smooth`, the
off-support Hessian, equation (1.43), the rooted sum, or the volume budget.
Those conclusions are generated by the assembler.

The strict `alpha_pos` field is the visible scalar denominator required by
the canonical volume rate.  It is stronger than the terminal nonnegativity
bookkeeping and is not a renamed `volume_budget`. -/
structure CMP116CenteredConditionedCombinedSourceProofs
    {Index : Type*} {nDelta M Q Nc n L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (P : Finset (CombinedSourceBond M Q))
    (Z : Finset (FinBox 4 (2 * Q)))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (baseCoarseCovariance :
      CombinedSourceCoarseField Q Nc →L[ℝ]
        CombinedSourceCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (D D₃ : CombinedSourceFineField M Q Nc →
      CombinedSourceCoarseField Q Nc)
    (V₀ : CombinedSourceFineField M Q Nc → ℝ)
    (Pprop T : CombinedSourceRectangularFieldMap M Q Nc)
    (DeltaPi : CombinedSourceFineField M Q Nc →L[ℝ]
      CombinedSourceFineField M Q Nc)
    (J : CombinedSourceFineField M Q Nc)
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J) where
  carrier_subset_sigmaZero :
    X.contourCarrier ⊆ cmp116SourceSigmaZero anchor
  carrier_subset_Z0 :
    X.contourCarrier ⊆
      cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P
  Z0_subset_Z :
    cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P ⊆ Z
  patchedDefect_small :
    ‖cmp99PatchedPhysicalParametrixDefect
        (cmp99SourcePi4Charts : Finset (CMP99SourcePi4Chart Unit Q))
        X.K cmp99SourcePi4ChartEnlarged
        (cmp99SourcePi4ChartCore (M := M))
        X.coercivity_pos X.mass_pos X.K_coercive‖ < 1
  Ahead_nonneg : 0 ≤ X.Ahead
  rho_nonneg : 0 ≤ X.rho
  rate_pos : 0 < X.rate
  shell_small : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-X.rate) < 1
  patchCertificate :
    CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts : Finset (CMP99SourcePi4Chart Unit Q))
      X.K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      X.coercivity_pos X.mass_pos X.K_coercive physicalBondDist
      X.Ahead X.rho X.rate
  distance_triangle : ∀ target source middle : CombinedSourceBond M Q,
    physicalBondDist target source ≤
      physicalBondDist target middle + physicalBondDist middle source
  degree_bound : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ X.Delta
  one_le_Delta : 1 ≤ X.Delta
  radius_nonneg : 0 ≤ X.radius
  radius_cap : ∀ i, 1 + X.base.deltaRadius i ≤ X.radius
  contour_series_small :
    ‖cmp116SourcePi4ComplexContourRatio
      X.Delta X.rho (1 + X.radius)‖ < 1
  neumann_small :
    ‖cmp116PhysicalEndomorphismComplexMatrix X.K‖ *
      cmp116SourcePi4PhysicalComplexContourDefectBound
        Nc X.Delta X.Ahead X.rho X.rate X.radius (1 + X.radius) < 1
  neumann_transpose_small :
    cmp116SourcePi4PhysicalComplexTransposeRelativeDefectBound
      X.K X.Delta X.Ahead X.rho X.rate X.radius (1 + X.radius) < 1
  qBound_nonneg : 0 ≤ X.qBound
  qBound_lt_one : X.qBound < 1
  E0Direct_nonneg : 0 ≤ X.E0Direct
  epsilon1_pos : 0 < X.epsilon1
  epsilon1_le_one : X.epsilon1 ≤ 1
  C1_pos : 0 < X.C1
  alpha4_pos : 0 < X.alpha4
  C3_nonneg : 0 ≤ X.C3
  C3_le : X.C3 ≤ X.E0 * X.C1
  one_le_M : 1 ≤ M
  eight_le_q : 8 ≤ X.q
  one_lt_kappa1 : 1 < X.kappa1
  source_budget :
    (1 - 3 * X.delta) * X.kappa ≤ (1 / 8 : ℝ) * (X.kappa1 - 1)
  exponential_row_bound : ∀ target : CombinedSourceBond M Q,
    ∑ source : CombinedSourceBond M Q,
      Real.exp (-(cmp116Eq219InternalRate M X.kappa1 *
        (physicalBondDist target source : ℝ))) ≤ X.rowSum
  hD : ContDiff ℝ ⊤ D
  hD₃ : ContDiff ℝ ⊤ D₃
  hV₀ : ContDiff ℝ ⊤ V₀
  sourceJetBound_nonneg : 0 ≤ X.sourceJetBound
  hC : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j, j ≤ 3 →
    ‖iteratedFDeriv ℝ j V₀
      (cmp102Eq80JointRemainderInner D
        (Pprop + t • T,
          cmp109ConstrainedLinearFluctuation
            (L := M) X.gk (0 : CombinedSourceFineField M Q Nc)))‖ ≤ X.C
  hRjet : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j,
    1 ≤ j → j ≤ 3 →
      ‖iteratedFDeriv ℝ j
          (fun z : CombinedSourceRectangularFieldMap M Q Nc ×
              CombinedSourceFineField M Q Nc => z.2)
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) X.gk (0 : CombinedSourceFineField M Q Nc))‖ +
        cmp102Eq80JointEvaluationJetMajorant D j
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) X.gk (0 : CombinedSourceFineField M Q Nc)) ≤
          X.Rjet ^ j
  hsourceJet : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
    cmp102Eq80JointPotentialSourceJetMajorant
        D D₃ DeltaPi J 3
        (Pprop + t • T,
          cmp109ConstrainedLinearFluctuation
            (L := M) X.gk (0 : CombinedSourceFineField M Q Nc))
        X.C X.Rjet ≤ X.sourceJetBound
  cardRatio_nonneg : 0 ≤ X.cardRatio
  metricRatio_nonneg : 0 ≤ X.metricRatio
  summationRatio_nonneg : 0 ≤ X.summationRatio
  walk_split :
    cmp102Eq80PhysicalFineHeadTailWalkRatio
        (M := M) baseCoarseCovariance X.Ahead X.rho X.rate
          (1 + X.radius) ≤
      X.cardRatio * (X.metricRatio * X.summationRatio)
  amplitude_nonneg : 0 ≤ X.C3 * X.epsilon1
  cardRate_nonneg : 0 ≤ cmp102Eq80Eq143CardRate M X.kappa1
  metricRate_nonneg : 0 ≤ cmp102Eq80Eq143MetricRate X.kappa1
  cardDecay :
    X.cardRatio ≤ Real.exp
      (-(cmp102Eq80Eq143CardRate M X.kappa1 * 10000))
  metricDecay :
    X.metricRatio ≤ Real.exp
      (-(cmp102Eq80Eq143MetricRate X.kappa1 * 10000))
  walk_small :
    ((cmp116SourcePi4TerminalBranching X.Delta : ℕ) : ℝ) *
      X.summationRatio < 1
  eq143_budget : CMP102Eq80CouplingScaledEq143ProducerBudget
    (M := M) baseCoarseCovariance X.sourceJetBound X.summationRatio
    layerWord X.Delta M X.gk X.kappa1 X.C3 X.epsilon1 X.C2
  residual_rate_nonneg : 0 ≤ (1 - 2 * X.delta) * X.kappa
  rooted_rate_nonneg : 0 ≤ X.delta * X.kappa
  animal_small :
    64 * Real.exp (-(((1 - 2 * X.delta) * X.kappa) / 24)) < 1
  rooted_animal_small :
    64 * Real.exp (-((X.delta * X.kappa) / 24)) < 1
  normalizedGap :
    ((((X.gapScale * M : ℕ) : ℝ) ^ 4)⁻¹ * (X.gapCard : ℝ)) =
      (nDelta : ℝ)
  deltaRadius_eq :
    X.base.deltaRadius = fun _ => cmp116Eq214SigmaCauchyRadius X.kappa1
  yRadius_eq :
    X.base.yRadius = fun Y =>
      cmp116Eq218TauAbsSolved X.E0 X.epsilon1 X.C1 X.alpha4 M X.q
        X.C2 X.kappa1 X.delta X.kappa
          (cmp116Eq80Lemma1CombinedDomainMetric anchor domains E Y : ℝ)
  alpha_pos : 0 < X.alpha
  root_small :
    X.alpha *
      (@norm
        (Matrix
          (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
          (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℝ)
        Matrix.instL2OpNormedAddCommGroup.toNorm
        (cmp116PhysicalEndomorphismRealMatrix X.root)) ^ 2 < 1
  gamma_nonneg : 0 ≤ X.gamma
  outer_small :
    2 *
      (cmp116SourcePi4PhysicalComplexR1DefectBilateralBudget
          X.K X.root X.coercivity_pos X.mass_pos X.K_coercive
          (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P)
          X.Delta X.Ahead X.rho X.rate X.radius (1 + X.radius) +
        |cmp116Eq225SourceCoefficient
            (cmp116PhysicalEndomorphismRealMatrix X.root) X.alpha *
          X.sourceRate|) ≤ X.qBound

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxHeartbeats 280000 in
/-- Genuine source-specific assembler for the pre-(1.36) record.

The caller supplies physical data and the still-open contour, parametrix,
jet, and scalar windows.  Every field listed in the live 18/41 producer map
is installed from a literal definition or an independent theorem.  No
inhabited `PreEq136`, ledger-identification record, free equation-(1.43)
estimate, rooted sum, or volume budget is an input. -/
noncomputable def
    cmp116Eq226CenteredConditionedCombinedSourcePreEq136
    {Index : Type*} {nDelta M Q Nc n L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (P : Finset (CombinedSourceBond M Q))
    (Z : Finset (FinBox 4 (2 * Q)))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (baseCoarseCovariance :
      CombinedSourceCoarseField Q Nc →L[ℝ]
        CombinedSourceCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (D D₃ : CombinedSourceFineField M Q Nc →
      CombinedSourceCoarseField Q Nc)
    (V₀ : CombinedSourceFineField M Q Nc → ℝ)
    (Pprop T : CombinedSourceRectangularFieldMap M Q Nc)
    (DeltaPi : CombinedSourceFineField M Q Nc →L[ℝ]
      CombinedSourceFineField M Q Nc)
    (J : CombinedSourceFineField M Q Nc)
    (X : CMP116CenteredConditionedCombinedSourceData (nDelta := nDelta)
      Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J)
    (H : CMP116CenteredConditionedCombinedSourceProofs Dict P Z anchor domains
      E V baseCoarseCovariance layerWord D D₃ V₀ Pprop T DeltaPi J X) :
    CMP116Eq226CenteredConditionedPhysicalTermSourcePreEq136
      (nDelta := nDelta)
      (nY := CMP116Eq80Lemma1CombinedDomainCount anchor domains E)
      Dict
      (cmp116Eq80Lemma1CombinedSourceSmallFieldCarrier anchor domains E)
      P (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P) Z := by
  let total := X.total
  let residual := X.residual
  let domainMetric := cmp116Eq80Lemma1CombinedDomainMetric anchor domains E
  let domainCard := cmp116Eq80Lemma1CombinedDomainCard anchor domains E
  let domainSupport := cmp116Eq80Lemma1CombinedDomainSupport anchor domains E
  let kernelSupport := cmp116Eq80Lemma1CombinedKernelSupport anchor domains E
  let E0 := X.E0
  let threshold := X.threshold
  let alpha := X.alpha
  let rootBound := X.rootBound
  let volumeRate := X.volumeRate
  refine {
    base := X.base
    anchor := anchor
    contourCarrier := X.contourCarrier
    carrier_subset_sigmaZero := H.carrier_subset_sigmaZero
    carrier_subset_Z0 := H.carrier_subset_Z0
    Z0_subset_Z := H.Z0_subset_Z
    contourEquiv := X.contourEquiv
    K := X.K
    root := X.root
    sourceRange := X.sourceRange
    sourceRange_bound := X.sourceRange_bound H.one_le_M
    finiteRange := X.finiteRange
    coercivityConstant := X.coercivityConstant
    mass := X.mass
    coercivity_pos := X.coercivity_pos
    mass_pos := X.mass_pos
    K_coercive := X.K_coercive
    patchedDefect_small := H.patchedDefect_small
    Ahead := X.Ahead
    rho := X.rho
    rate := X.rate
    radius := X.radius
    Ahead_nonneg := H.Ahead_nonneg
    rho_nonneg := H.rho_nonneg
    rate_pos := H.rate_pos
    shell_small := H.shell_small
    patchCertificate := H.patchCertificate
    distance_triangle := H.distance_triangle
    Delta := X.Delta
    degree_bound := H.degree_bound
    one_le_Delta := H.one_le_Delta
    radius_nonneg := H.radius_nonneg
    radius_cap := H.radius_cap
    contour_series_small := H.contour_series_small
    neumann_small := H.neumann_small
    neumann_transpose_small := H.neumann_transpose_small
    total := total
    residual := residual
    smooth := by
      simpa [total, residual,
        CMP116CenteredConditionedCombinedSourceData.total,
        CMP116CenteredConditionedCombinedSourceData.residual] using
        (fun sigma psi phi =>
          contDiff_cmp116CenteredConditionedCombinedEq80PartialQuadraticCore
            X.base.spectatorSupport X.base.fluctuationSupport anchor domains E V
            X.contourCarrier X.contourEquiv X.K X.coercivity_pos X.mass_pos
            X.K_coercive baseCoarseCovariance sigma psi phi layerWord X.choice
            D D₃ V₀ Pprop T DeltaPi J X.gk)
    kernelSupport := kernelSupport
    domainMetric := domainMetric
    domainCard := domainCard
    domainSupport := domainSupport
    E0 := E0
    epsilon1 := X.epsilon1
    C1 := X.C1
    alpha4 := X.alpha4
    C3 := X.C3
    C2 := X.C2
    kappa1 := X.kappa1
    delta := X.delta
    kappa := X.kappa
    gk := X.gk
    rowSum := X.rowSum
    threshold := threshold
    alpha := alpha
    gamma := X.gamma
    q := X.q
    gapScale := X.gapScale
    gapCard := X.gapCard
    qBound := X.qBound
    qBound_nonneg := H.qBound_nonneg
    qBound_lt_one := H.qBound_lt_one
    rootBound := rootBound
    volumeRate := volumeRate
    conditionedCovariance := X.conditionedCovariance
    conditionedRoot := X.conditionedRoot
    conditionedCovariance_nondegenerate :=
      X.conditionedCovariance_nondegenerate
    E0_pos := by
      dsimp [E0, CMP116CenteredConditionedCombinedSourceData.E0]
      exact add_pos_of_nonneg_of_pos H.E0Direct_nonneg X.lemma1.E0_pos
    epsilon1_pos := H.epsilon1_pos
    C1_pos := H.C1_pos
    alpha4_pos := H.alpha4_pos
    C3_nonneg := H.C3_nonneg
    C3_le := by simpa [E0] using H.C3_le
    one_le_M := H.one_le_M
    eight_le_q := H.eight_le_q
    one_lt_kappa1 := H.one_lt_kappa1
    source_budget := H.source_budget
    domainMetric_nonneg := by
      simpa [domainMetric] using
        cmp116Eq80Lemma1CombinedDomainMetric_nonneg anchor domains E
    exponential_row_bound := H.exponential_row_bound
    metric_budget := by
      simpa [kernelSupport, domainCard] using
        cmp116Eq80Lemma1CombinedKernelSupport_metricBudget
          anchor domains E (le_of_lt H.one_lt_kappa1)
    hessian_zero_off_support := by
      simpa [total, residual, kernelSupport,
        CMP116CenteredConditionedCombinedSourceData.total,
        CMP116CenteredConditionedCombinedSourceData.residual] using
        cmp116CenteredConditionedCombinedEq80_hessian_zero_off_support
          X.base.spectatorSupport X.base.fluctuationSupport anchor domains E V
          X.contourCarrier X.contourEquiv X.base.deltaRadius
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
            (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P))
          X.K X.coercivity_pos X.mass_pos X.K_coercive baseCoarseCovariance
          layerWord X.choice D D₃ V₀ Pprop T DeltaPi J X.gk
    eq143 := by
      simpa [total, residual, domainMetric, domainCard,
        CMP116CenteredConditionedCombinedSourceData.total,
        CMP116CenteredConditionedCombinedSourceData.residual] using
        cmp116CenteredConditionedCombinedEq80_terminal_eq143
          X.base.spectatorSupport X.base.fluctuationSupport anchor domains E V
          X.contourCarrier X.contourEquiv X.base.deltaRadius
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
            (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P))
          X.radius H.radius_nonneg H.radius_cap X.K X.coercivity_pos X.mass_pos
          X.K_coercive baseCoarseCovariance H.Ahead_nonneg H.rho_nonneg
          H.rate_pos H.shell_small H.patchCertificate
          (X.sourceRange_bound H.one_le_M)
          H.degree_bound H.one_le_Delta H.contour_series_small layerWord
          X.choice D D₃ V₀ Pprop T DeltaPi J X.gk H.hD H.hD₃ H.hV₀
          X.C X.Rjet X.sourceJetBound H.sourceJetBound_nonneg H.hC H.hRjet
          H.hsourceJet H.cardRatio_nonneg H.metricRatio_nonneg
          H.summationRatio_nonneg H.walk_split X.kappa1 X.C3 X.epsilon1
          X.C2 H.amplitude_nonneg H.cardRate_nonneg H.metricRate_nonneg
          H.cardDecay H.metricDecay H.walk_small H.eq143_budget
    interaction_budget := by
      simpa [alpha, CMP116CenteredConditionedCombinedSourceData.alpha,
        CMP116CenteredConditionedCombinedSourceData.potentialRate,
        CMP116CenteredConditionedCombinedSourceData.r2Rate] using
        cmp116Eq226_optimalInteractionAlpha_budget
          X.potentialRate X.r2Rate X.gamma
    deltaRadius_eq := by
      change X.base.deltaRadius = fun _ =>
        cmp116Eq214SigmaCauchyRadius X.kappa1
      exact H.deltaRadius_eq
    normalizedGap := H.normalizedGap
    yRadius_eq := by
      change X.base.yRadius = fun Y =>
        cmp116Eq218TauAbsSolved X.E0 X.epsilon1 X.C1 X.alpha4 M X.q
          X.C2 X.kappa1 X.delta X.kappa
            (cmp116Eq80Lemma1CombinedDomainMetric anchor domains E Y : ℝ)
      exact H.yRadius_eq
    gk_ne := X.lemma1.gk_pos.ne'
    threshold_eq := by rfl
    alpha_nonneg := le_of_lt H.alpha_pos
    root_small := by simpa [alpha] using H.root_small
    gamma_nonneg := H.gamma_nonneg
    threshold_nonneg := by
      dsimp [threshold, CMP116CenteredConditionedCombinedSourceData.threshold]
      exact div_nonneg X.lemma1.epsilon1_nonneg (le_of_lt X.lemma1.gk_pos)
    outer_small := by
      simpa [alpha, CMP116CenteredConditionedCombinedSourceData.alpha,
        CMP116CenteredConditionedCombinedSourceData.sourceRate] using H.outer_small
    domain_nonempty := by
      simpa [domainSupport] using
        cmp116Eq80Lemma1CombinedDomainSupport_nonempty anchor domains E
    domain_subset := by
      simpa [domainSupport] using
        cmp116Eq80Lemma1CombinedDomainSupport_subset_combinedCenteredRegion
          anchor domains E P
    rootBound_nonneg := by
      have hE0 : 0 ≤ E0 := le_of_lt (add_pos_of_nonneg_of_pos
        H.E0Direct_nonneg X.lemma1.E0_pos)
      simpa [rootBound, CMP116CenteredConditionedCombinedSourceData.rootBound,
        E0] using
        cmp116Eq80Lemma1CombinedPhysicalRootBound_nonneg (q := X.q)
          hE0 (le_of_lt H.epsilon1_pos) (le_of_lt H.C1_pos)
          (le_of_lt H.alpha4_pos) H.animal_small H.rooted_animal_small
    rooted_residual := by
      intro i hi
      have hE0 : 0 ≤ E0 := le_of_lt (add_pos_of_nonneg_of_pos
        H.E0Direct_nonneg X.lemma1.E0_pos)
      simpa [domainSupport, domainMetric, rootBound,
        CMP116CenteredConditionedCombinedSourceData.rootBound, E0] using
        cmp116Eq80Lemma1Combined_rooted_residual_le_physical (q := X.q)
          anchor domains E E0 X.epsilon1 X.C1 X.C2 X.kappa1 X.delta
          X.kappa X.alpha4 hE0 (le_of_lt H.epsilon1_pos)
          (le_of_lt H.C1_pos) (le_of_lt H.alpha4_pos)
          H.residual_rate_nonneg H.rooted_rate_nonneg H.animal_small
          H.rooted_animal_small i
    volume_budget := by
      simpa [rootBound, volumeRate,
        CMP116CenteredConditionedCombinedSourceData.rootBound,
        CMP116CenteredConditionedCombinedSourceData.volumeRate,
        CMP116CenteredConditionedCombinedSourceData.sourceRate,
        CMP116CenteredConditionedCombinedSourceData.determinantCost,
        alpha, E0] using
        cmp116Eq80Lemma1CombinedPhysical_volume_budget (q := X.q)
          X.K X.root X.coercivity_pos X.mass_pos X.K_coercive
          (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P)
          X.Delta X.radius X.rate X.Ahead X.rho alpha X.sourceRate X.qBound
          X.determinantCost E0 X.epsilon1 X.C1 X.C2 X.kappa1 X.delta
          X.kappa X.alpha4 H.alpha_pos
  }

end

end YangMills.RG
