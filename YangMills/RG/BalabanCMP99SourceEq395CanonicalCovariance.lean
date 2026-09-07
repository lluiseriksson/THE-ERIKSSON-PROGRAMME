/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395PatchedCovarianceDecay
import YangMills.RG.BalabanCMP99SourceEq395CovarianceOnSourceDecay

/-!
# Identification of the CMP99 (3.95) Neumann sum with the canonical covariance

The source-generated coarse covariance already exists canonically as the
coercive inverse of `Q' G'^2 Q'^*`.  Equation (3.95) constructs the same
inverse by a patched parametrix and an exhaustive Neumann correction.  This
file identifies the two operators exactly.

Consequently the volume-independent decay estimate for the corrected
parametrix is a theorem about the canonical source covariance itself, rather
than about a parallel inverse candidate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- The canonical generated coarse covariance, realized on the full ambient
coarse torus used by equation (3.95). -/
noncomputable def cmp99Eq395PhysicalCanonicalCovariance
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) : CMP99Eq395AmbientOperator Q Nc :=
  let Omega := cmp99Eq395FullCoarseRegion (Q := Q)
  (extendZeroZeroCLM Omega).comp
    ((cmp99Eq395GeneratedPhysicalCovarianceOnSource Omega hM depth hspacing
      background budget fineSmall hsmall).comp (restrictZeroCLM Omega))

omit [NeZero Nc] in
/-- On the full source region, zero extension followed by restriction is the
ambient identity. -/
theorem cmp99Eq395FullCoarseRegion_extendZero_comp_restrict_eq_id :
    let Omega := cmp99Eq395FullCoarseRegion (Q := Q)
    (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega).comp
        (restrictZeroCLM (𝔤 := SUNLieCoord Nc) Omega) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc)) := by
  dsimp only
  let Omega := cmp99Eq395FullCoarseRegion (Q := Q)
  rw [activeGaugeRegion_extendZero_comp_restrict_eq_multiplier]
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp [finitePiLpScalarMultiplier_apply, cmp99Eq395FullCoarseRegion]

/-- The canonical source covariance is also a left inverse of the generated
middle after transport to the original source coordinates. -/
theorem cmp99Eq395GeneratedPhysicalCovarianceOnSource_comp_middle
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    (cmp99Eq395GeneratedPhysicalCovarianceOnSource Omega hM depth hspacing
      background budget fineSmall hsmall).comp
      (cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
        background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ _ := by
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    Omega (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  rw [← cmp99Eq395GeneratedPhysicalMiddleDirect_eq_onSource
    Omega hM depth hspacing background budget fineSmall hsmall]
  have hinverse : C.comp Middle = ContinuousLinearMap.id ℝ _ :=
    cmp99SourceGeneratedPhysicalCoarseCovariance_comp_middle
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall
  change (cmp99SourceTerminalCLMTransport hs hs C).comp
      (cmp99SourceTerminalCLMTransport hs hs Middle) = _
  rw [cmp99SourceTerminalCLMTransport_comp, hinverse]
  exact cmp99SourceTerminalCLMTransport_id hs

/-- The ambient canonical covariance is a left inverse of the literal global
middle of equation (3.95). -/
theorem cmp99Eq395PhysicalCanonicalCovariance_comp_globalMiddle_eq_id
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    (cmp99Eq395PhysicalCanonicalCovariance hM depth hspacing background budget
      fineSmall hsmall).comp
      (cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
        fineSmall hsmall) =
      ContinuousLinearMap.id ℝ _ := by
  let Omega := cmp99Eq395FullCoarseRegion (Q := Q)
  let E := extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  let R := restrictZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  let C := cmp99Eq395GeneratedPhysicalCovarianceOnSource Omega hM depth hspacing
    background budget fineSmall hsmall
  let A := cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
    background budget fineSmall hsmall
  have hRE : R.comp E = ContinuousLinearMap.id ℝ _ :=
    activeGaugeRegion_restrictZero_comp_extendZero Omega
  have hER : E.comp R = ContinuousLinearMap.id ℝ _ :=
    cmp99Eq395FullCoarseRegion_extendZero_comp_restrict_eq_id
  have hCA : C.comp A = ContinuousLinearMap.id ℝ _ :=
    cmp99Eq395GeneratedPhysicalCovarianceOnSource_comp_middle Omega hM depth
      hspacing background budget fineSmall hsmall
  rw [cmp99Eq395PhysicalCanonicalCovariance,
    cmp99Eq395PhysicalGlobalMiddle_eq_extend_onSource]
  change (E.comp (C.comp R)).comp (E.comp (A.comp R)) = _
  simp only [ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc R E (A.comp R), hRE,
    ContinuousLinearMap.id_comp,
    ← ContinuousLinearMap.comp_assoc C A R, hCA,
    ContinuousLinearMap.id_comp, hER]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
/-- Exact source identification: the exhaustive Neumann construction of
(3.95) is the canonical coercive covariance. -/
theorem cmp99Eq395PhysicalCorrectedCovariance_eq_canonical
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (hcontract : cmp99Eq395PhysicalGroupedNeumannRatio
      M depth spacing epsilon < 1) :
    cmp99Eq395PhysicalCorrectedCovariance D hpi5 P hM depth hspacing
        background budget fineSmall hsmall =
      cmp99Eq395PhysicalCanonicalCovariance hM depth hspacing background budget
        fineSmall hsmall := by
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
    fineSmall hsmall
  let Ccorr := cmp99Eq395PhysicalCorrectedCovariance D hpi5 P hM depth
    hspacing background budget fineSmall hsmall
  let Ccan := cmp99Eq395PhysicalCanonicalCovariance hM depth hspacing
    background budget fineSmall hsmall
  have hACcorr : A.comp Ccorr = ContinuousLinearMap.id ℝ _ :=
    cmp99Eq395PhysicalGlobalMiddle_comp_correctedCovariance_eq_id
      D hpi5 P hM depth hspacing background budget fineSmall hsmall
        (lt_of_le_of_lt
          (norm_cmp99Eq395PhysicalCorrection_le_groupedNeumannRatio
            D hpi5 P hM depth hspacing background budget fineSmall hsmall)
          hcontract)
  have hCcanA : Ccan.comp A = ContinuousLinearMap.id ℝ _ :=
    cmp99Eq395PhysicalCanonicalCovariance_comp_globalMiddle_eq_id hM depth
      hspacing background budget fineSmall hsmall
  calc
    Ccorr = (ContinuousLinearMap.id ℝ _).comp Ccorr := by
      rw [ContinuousLinearMap.id_comp]
    _ = (Ccan.comp A).comp Ccorr := by rw [hCcanA]
    _ = Ccan.comp (A.comp Ccorr) := ContinuousLinearMap.comp_assoc _ _ _
    _ = Ccan.comp (ContinuousLinearMap.id ℝ _) := by rw [hACcorr]
    _ = Ccan := by rw [ContinuousLinearMap.comp_id]

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
