/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalIndexedEq143
import YangMills.RG.BalabanCMP116CenteredConditionedCombinedEq80PartialPotential
import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedKernelSupport

/-!
# Hessian support on the direct/native CMP116 ledger

**VALIDATED INTERMEDIATE BRICK.** This source and its public audit were
materialized from source checkpoint `134a21f0` in one fresh Colab Pro+ clone;
the focal queue, `YangMillsCore`, and the full oracle all exited zero.  The
evidence archive has SHA-256 `589769BC64D24493B0F68F5B0458DB017258919B32C265D8C83FA327487233EC`.

The direct equation-(80) quadratic core is the diagonal of a bilinear form
precomposed in both slots with the bilateral physical-bond projection of its
domain.  Hence a matrix element vanishes whenever either bond is outside that
domain support.

On a native CMP109 Lemma-1 index the same literal residual occurs in `total`
and `residual`, so the quadratic core and its Hessian are identically zero.
Together these two facts discharge the terminal `hessian_zero_off_support`
shape for the literal combined kernel support; no locality hypothesis on the
native residual and no free off-support estimate is used.

The native cancellation is an exact theorem about the assembled ledger.  It
does not, by itself, prove from CMP109 that the Lemma-1 activity has no
independent quadratic contribution; that source identification is the reason
the same literal native residual is installed on both sides of the ledger and
must remain visible in the constructor audit.
-/

namespace YangMills.RG

noncomputable section

private abbrev CombinedHessianSupportFineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CombinedHessianSupportCoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev CombinedHessianSupportRectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CombinedHessianSupportCoarseField Q Nc →L[ℝ]
    CombinedHessianSupportFineField M Q Nc

private abbrev CombinedHessianSupportBond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

/-- A projected quadratic diagonal has zero Hessian matrix element as soon as
one projected direction is zero. -/
private theorem cmp116FDerivHessian_half_projectedBilinearDiagonal_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : F →L[ℝ] F →L[ℝ] ℝ) (P : F →L[ℝ] F)
    (x u v : F) (hoff : P u = 0 ∨ P v = 0) :
    cmp116FDerivHessian
        (fun z => (1 / 2 : ℝ) * H (P z) (P z)) x u v = 0 := by
  let HP : F →L[ℝ] F →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ F F ℝ).flip P).comp (H.comp P)
  have hfun :
      (fun z : F => (1 / 2 : ℝ) * H (P z) (P z)) =
        fun z => (1 / 2 : ℝ) * HP z z := by
    funext z
    simp [HP]
  rw [hfun, cmp116FDerivHessian_half_bilinearDiagonal]
  rcases hoff with hu | hv
  · simp [HP, hu]
  · simp [HP, hv]

/-- A fixed continuous bilinear form precomposed in both arguments with a
continuous linear projection has a smooth quadratic diagonal. -/
private theorem contDiff_half_projectedBilinearDiagonal
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : F →L[ℝ] F →L[ℝ] ℝ) (P : F →L[ℝ] F) (k : WithTop ℕ∞) :
    ContDiff ℝ k (fun z => (1 / 2 : ℝ) * H (P z) (P z)) := by
  have hleft : ContDiff ℝ k (fun z => H (P z)) := H.contDiff.comp P.contDiff
  have hdiag : ContDiff ℝ k (fun z => H (P z) (P z)) :=
    hleft.clm_apply P.contDiff
  simpa [smul_eq_mul] using hdiag.const_smul (1 / 2 : ℝ)

/-- The literal combined direct/native quadratic core is `C²` without a
separate smoothness premise.  Direct cores are fixed projected quadratic
diagonals; native cores are constant zero. -/
theorem contDiff_cmp116CenteredConditionedCombinedEq80PartialQuadraticCore
    {Index : Type*} {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport :
      Finset (CombinedHessianSupportBond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K : CombinedHessianSupportFineField M Q Nc →L[ℝ]
      CombinedHessianSupportFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedHessianSupportCoarseField Q Nc →L[ℝ]
        CombinedHessianSupportCoarseField Q Nc)
    (sigma : Fin nDelta → ℂ)
    (psi : RestrictedField spectatorSupport (fun _ => SUNLieCoord Nc))
    (phi : RestrictedField fluctuationSupport (fun _ => SUNLieCoord Nc))
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CombinedHessianSupportFineField M Q Nc →
      CombinedHessianSupportCoarseField Q Nc)
    (V₀ : CombinedHessianSupportFineField M Q Nc → ℝ)
    (Pprop T : CombinedHessianSupportRectangularFieldMap M Q Nc)
    (DeltaPi : CombinedHessianSupportFineField M Q Nc →L[ℝ]
      CombinedHessianSupportFineField M Q Nc)
    (J : CombinedHessianSupportFineField M Q Nc)
    (gk : ℝ) :
    ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore
        (cmp116CenteredConditionedCombinedEq80PartialTotal
          spectatorSupport fluctuationSupport anchor domains E V
          contourCarrier e K hc hmass hK baseCoarseCovariance
          layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma psi phi)
        (cmp116CenteredConditionedCombinedEq80PartialResidual
          spectatorSupport fluctuationSupport anchor domains E V
          contourCarrier e K hc hmass hK baseCoarseCovariance
          layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma psi phi) y) := by
  apply contDiff_cmp116Eq142PhysicalQuadraticCore_combined
  intro i
  let Y := cmp102Eq80SourcePi4IndexedLocalizationDomain
    (M := M) anchor domains i
  let f : CombinedHessianSupportFineField M Q Nc → ℝ := fun A =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
      layerWord choice D D₃ V₀ Pprop T DeltaPi J A Y.blocks
  let PY : CombinedHessianSupportFineField M Q Nc →L[ℝ]
      CombinedHessianSupportFineField M Q Nc :=
    physicalBondProjection (Nc := Nc) Y.bondSupport
  have hcore :
      cmp116Eq142PhysicalQuadraticCore
          (cmp102Eq80PhysicalIndexedContourTotal
            anchor domains contourCarrier e K hc hmass hK
            baseCoarseCovariance sigma layerWord choice
            D D₃ V₀ Pprop T DeltaPi J gk)
          (fun j =>
            cmp102Eq80PhysicalIndexedContourResidual
              anchor domains contourCarrier e j K hc hmass hK
              baseCoarseCovariance sigma layerWord choice
              D D₃ V₀ Pprop T DeltaPi J gk)
          i =
        fun B => (1 / 2 : ℝ) *
          cmp116FDerivHessian (cmp102Eq80CouplingScaledPotential gk f) 0
            (PY B) (PY B) := by
    funext B
    simpa [Y, f, PY] using
      (cmp116Eq142PhysicalQuadraticCore_indexedContour_eq_half_projectedHessian
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice D D₃ V₀ Pprop T
        DeltaPi J gk B)
  rw [hcore]
  exact contDiff_half_projectedBilinearDiagonal
    (cmp116FDerivHessian (cmp102Eq80CouplingScaledPotential gk f) 0) PY 2

/-- The Hessian of the literal combined direct/native quadratic core vanishes
off the literal combined kernel support.  The base point is arbitrary, so the
result applies directly at the terminal radial point. -/
theorem
    cmp116CenteredConditionedCombinedEq80PartialHessian_zero_off_kernelSupport
    {Index : Type*} {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport :
      Finset (CombinedHessianSupportBond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K : CombinedHessianSupportFineField M Q Nc →L[ℝ]
      CombinedHessianSupportFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedHessianSupportCoarseField Q Nc →L[ℝ]
        CombinedHessianSupportCoarseField Q Nc)
    (sigma : Fin nDelta → ℂ)
    (psi : RestrictedField spectatorSupport (fun _ => SUNLieCoord Nc))
    (phi : RestrictedField fluctuationSupport (fun _ => SUNLieCoord Nc))
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CombinedHessianSupportFineField M Q Nc →
      CombinedHessianSupportCoarseField Q Nc)
    (V₀ : CombinedHessianSupportFineField M Q Nc → ℝ)
    (Pprop T : CombinedHessianSupportRectangularFieldMap M Q Nc)
    (DeltaPi : CombinedHessianSupportFineField M Q Nc →L[ℝ]
      CombinedHessianSupportFineField M Q Nc)
    (J : CombinedHessianSupportFineField M Q Nc)
    (gk : ℝ)
    (x : CombinedHessianSupportFineField M Q Nc) :
    ∀ y source target,
      ¬ cmp116Eq80Lemma1CombinedKernelSupport anchor domains E
          y source target →
        ∀ (v w : SUNLieCoord Nc),
          cmp116FDerivHessian
            (cmp116Eq142PhysicalQuadraticCore
              (cmp116CenteredConditionedCombinedEq80PartialTotal
                spectatorSupport fluctuationSupport anchor domains E V
                contourCarrier e K hc hmass hK baseCoarseCovariance
                layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma psi phi)
              (cmp116CenteredConditionedCombinedEq80PartialResidual
                spectatorSupport fluctuationSupport anchor domains E V
                contourCarrier e K hc hmass hK baseCoarseCovariance
                layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma psi phi)
              y)
            x
            (singlePhysicalBondCochain
              (d := 4) (N := M * (2 * Q)) (Nc := Nc) source v)
            (singlePhysicalBondCochain
              (d := 4) (N := M * (2 * Q)) (Nc := Nc) target w) = 0 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · intro source target hsupp v w
    let Y := cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor domains i
    let f : CombinedHessianSupportFineField M Q Nc → ℝ := fun A =>
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
        layerWord choice D D₃ V₀ Pprop T DeltaPi J A Y.blocks
    let PY : CombinedHessianSupportFineField M Q Nc →L[ℝ]
        CombinedHessianSupportFineField M Q Nc :=
      physicalBondProjection (Nc := Nc) Y.bondSupport
    have hcore :
        cmp116Eq142PhysicalQuadraticCore
            (cmp116CenteredConditionedCombinedEq80PartialTotal
              spectatorSupport fluctuationSupport anchor domains E V
              contourCarrier e K hc hmass hK baseCoarseCovariance
              layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma psi phi)
            (cmp116CenteredConditionedCombinedEq80PartialResidual
              spectatorSupport fluctuationSupport anchor domains E V
              contourCarrier e K hc hmass hK baseCoarseCovariance
              layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma psi phi)
            (Fin.castAdd (CMP109Lemma1NativeDomainCount E) i) =
          fun B => (1 / 2 : ℝ) *
            cmp116FDerivHessian (cmp102Eq80CouplingScaledPotential gk f) 0
              (PY B) (PY B) := by
      funext B
      simpa [Y, f, PY] using
        (cmp116Eq142PhysicalQuadraticCore_indexedContour_eq_half_projectedHessian
          anchor domains contourCarrier e i K hc hmass hK
          baseCoarseCovariance sigma layerWord choice D D₃ V₀ Pprop T
          DeltaPi J gk B)
    rw [hcore]
    have hsupp' :
        ¬ (source ∈ Y.bondSupport ∧ target ∈ Y.bondSupport) := by
      simpa [Y] using hsupp
    have hoff :
        PY (singlePhysicalBondCochain
              (d := 4) (N := M * (2 * Q)) (Nc := Nc) source v) = 0 ∨
          PY (singlePhysicalBondCochain
              (d := 4) (N := M * (2 * Q)) (Nc := Nc) target w) = 0 := by
      rcases not_and_or.mp hsupp' with hsource | htarget
      · exact Or.inl (by
          simpa [PY] using
            physicalBondProjection_single_not_mem Y.bondSupport source v
              hsource)
      · exact Or.inr (by
          simpa [PY] using
            physicalBondProjection_single_not_mem Y.bondSupport target w
              htarget)
    exact cmp116FDerivHessian_half_projectedBilinearDiagonal_eq_zero
      (cmp116FDerivHessian (cmp102Eq80CouplingScaledPotential gk f) 0)
      PY x
      (singlePhysicalBondCochain source v)
      (singlePhysicalBondCochain target w) hoff
  · intro source target _hsupp v w
    have hcore :
        cmp116Eq142PhysicalQuadraticCore
            (cmp116CenteredConditionedCombinedEq80PartialTotal
              spectatorSupport fluctuationSupport anchor domains E V
              contourCarrier e K hc hmass hK baseCoarseCovariance
              layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma psi phi)
            (cmp116CenteredConditionedCombinedEq80PartialResidual
              spectatorSupport fluctuationSupport anchor domains E V
              contourCarrier e K hc hmass hK baseCoarseCovariance
              layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma psi phi)
            (Fin.natAdd (CMP102Eq80SourcePi4DomainCount anchor domains) i) =
          (fun _ : CombinedHessianSupportFineField M Q Nc => (0 : ℝ)) := by
      funext B
      simpa using
        (cmp116Eq142PhysicalQuadraticCore_combined_native
          (cmp102Eq80PhysicalIndexedContourTotal
            anchor domains contourCarrier e K hc hmass hK
            baseCoarseCovariance sigma layerWord choice
            D D₃ V₀ Pprop T DeltaPi J gk)
          (fun j =>
            cmp102Eq80PhysicalIndexedContourResidual
              anchor domains contourCarrier e j K hc hmass hK
              baseCoarseCovariance sigma layerWord choice
              D D₃ V₀ Pprop T DeltaPi J gk)
          (cmp109Lemma1IndexedSourceResidual E V gk D) i B)
    rw [hcore]
    simp [cmp116FDerivHessian]

/-- Terminal-field form of the preceding support theorem.  The shifted
polydisc and radial-segment hypotheses are retained because the equation-(2.26)
record quantifies over them, but the exact quadratic support identity does not
need either hypothesis. -/
theorem
    cmp116CenteredConditionedCombinedEq80_hessian_zero_off_support
    {Index : Type*} {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport :
      Finset (CombinedHessianSupportBond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (deltaRadius : Fin nDelta → ℝ)
    (interiorBonds : Finset (CombinedHessianSupportBond M Q))
    (K : CombinedHessianSupportFineField M Q Nc →L[ℝ]
      CombinedHessianSupportFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedHessianSupportCoarseField Q Nc →L[ℝ]
        CombinedHessianSupportCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CombinedHessianSupportFineField M Q Nc →
      CombinedHessianSupportCoarseField Q Nc)
    (V₀ : CombinedHessianSupportFineField M Q Nc → ℝ)
    (Pprop T : CombinedHessianSupportRectangularFieldMap M Q Nc)
    (DeltaPi : CombinedHessianSupportFineField M Q Nc →L[ℝ]
      CombinedHessianSupportFineField M Q Nc)
    (J : CombinedHessianSupportFineField M Q Nc)
    (gk : ℝ) :
    ∀ psi phi sigma,
      CMP116Eq214ShiftedPolydisc nDelta deltaRadius sigma →
      ∀ b y source target,
        ¬ cmp116Eq80Lemma1CombinedKernelSupport anchor domains E
            y source target →
          ∀ (v w : SUNLieCoord Nc), ∀ t ∈ Set.Icc (0 : ℝ) 1,
            cmp116FDerivHessian
              (cmp116Eq142PhysicalQuadraticCore
                (cmp116CenteredConditionedCombinedEq80PartialTotal
                  spectatorSupport fluctuationSupport anchor domains E V
                  contourCarrier e K hc hmass hK baseCoarseCovariance
                  layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma
                  (restrictGlobal spectatorSupport psi)
                  (restrictGlobal fluctuationSupport phi))
                (cmp116CenteredConditionedCombinedEq80PartialResidual
                  spectatorSupport fluctuationSupport anchor domains E V
                  contourCarrier e K hc hmass hK baseCoarseCovariance
                  layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma
                  (restrictGlobal spectatorSupport psi)
                  (restrictGlobal fluctuationSupport phi)) y)
              (t • physicalBondProjection interiorBonds
                (cmp116SourcePhysicalCoordinateCochain b))
              (singlePhysicalBondCochain
                (d := 4) (N := M * (2 * Q)) (Nc := Nc) source v)
              (singlePhysicalBondCochain
                (d := 4) (N := M * (2 * Q)) (Nc := Nc) target w) = 0 := by
  intro psi phi sigma _hsigma b y source target hsupp v w t _ht
  exact
    cmp116CenteredConditionedCombinedEq80PartialHessian_zero_off_kernelSupport
      spectatorSupport fluctuationSupport anchor domains E V contourCarrier e
      K hc hmass hK baseCoarseCovariance sigma
      (restrictGlobal spectatorSupport psi)
      (restrictGlobal fluctuationSupport phi) layerWord choice D D₃ V₀ Pprop T
      DeltaPi J gk
      (t • physicalBondProjection interiorBonds
        (cmp116SourcePhysicalCoordinateCochain b))
      y source target hsupp v w

end

end YangMills.RG
