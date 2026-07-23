/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexPhysicalWalkMatrix
import YangMills.RG.BalabanCMP116Eq214ContourRelativeNorm
import YangMills.RG.BalabanCMP116Eq214PhysicalContourWalkCovariance
import YangMills.RG.BalabanCMP116SourceComplexCauchyWalkKernel

/-!
# Source CMP116 Cauchy bound in literal matrix form

The source-specific patched-parametrix theorem already supplies a closed,
volume-uniform Cauchy bound for every physical kernel coefficient.  This
module exposes that theorem in the matrix convention used by the physical
contour density.  Rows are target/output coordinates and columns are
source/input coordinates; no scalar coefficient remains as an independent
interface.
-/

namespace YangMills.RG

noncomputable section

universe u

open scoped Matrix.Norms.Operator

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-- The fixed-rate source Cauchy estimate, expressed directly as an entry of
the literal complex physical walk matrix. -/
theorem cmp116Eq214CauchyBoundaryBound_sourceSigmaZeroPi4PhysicalWalkMatrix_entry
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {M Q Nc Rrange NR : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q) (hsourceRange : Rrange + 1 ≤ 4 * M)
    (K : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc)
    {Cker c mass κ σ μ : ℝ}
    (hCker : 0 ≤ Cker) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ) (hμ : 0 < μ)
    (hgeomBase :
      ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-σ) < 1)
    (hgeomHead :
      ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-((κ - σ) - μ)) < 1)
    (hgeomContinuation :
      ((2 ^ 4 : ℕ) : ℝ) *
        Real.exp (-((((κ - σ) - σ) - σ) - μ)) < 1)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist Rrange)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => Cker))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond 4 (M * (2 * Q)),
      (Finset.univ.filter
        (fun y => physicalBondDist x y ≤ Rrange)).card ≤ NR)
    (htilt :
      (Cker + |mass|) *
          (Real.exp (κ * (Rrange : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (Δ : ℕ) (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ) :
    let Dict := cmp116SourceSigmaZeroPi4PhysicalChartDictionary
      (Label := Label) anchor hsourceRange
    let Ahead := cmp99PhysicalPatchHeadWeightedAmplitude c mass
      (cmp99PhysicalBondGeometricRowSum 4 σ)
      (cmp99PhysicalBondGeometricRowSum 4 ((κ - σ) - μ))
    let rho := cmp99PhysicalPatchContinuationWeightedAmplitude
      Cker κ Rrange c mass
      (cmp99PhysicalBondGeometricRowSum 4 σ)
      (cmp99PhysicalBondGeometricRowSum 4
        ((((κ - σ) - σ) - σ) - μ))
    let branching : ℕ :=
      Fintype.card Label * (625 * 626 * Δ ^ 1250)
    ∀ (left : ↥Dict.charts)
      {n : ℕ} (emb : Fin n ↪ FinBox 4 (2 * Q))
      (radius : Fin n → ℝ)
      (row col :
        CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (Rweak : ℝ) (hRweak : 1 ≤ Rweak)
      (hcap : ∀ i, 1 + radius i ≤ Rweak)
      (hsmall :
        (branching : ℝ) * rho * Rweak ^ 10000 < 1),
      CMP116Eq214CauchyBoundaryBound n radius
        (fun z =>
          cmp116ComplexPhysicalWalkContourMatrix emb
            (fun walk : CMP99AnchoredWalk
                (cmp99PhysicalPatchSuccessorSteps
                  Dict.charts Dict.core Dict.enlarged
                  physicalBondDist Rrange) left =>
              walk.active Dict.domainActive)
            (fun walk =>
              walk.term
                (cmp99PhysicalPatchHead Dict.charts K
                  Dict.enlarged Dict.core hc hmass hK)
                (fun _ => cmp99PhysicalPatchContinuation Dict.charts K
                  Dict.enlarged Dict.core hc hmass hK))
            z row col)
        ((Ahead *
            Real.exp (-(μ *
              (physicalBondDist row.1 col.1 : ℝ))) *
            Rweak ^ 10000) *
          (1 - (branching : ℝ) * rho * Rweak ^ 10000)⁻¹) := by
  dsimp only
  intro left n emb radius row col Rweak hRweak hcap hsmall
  simpa [cmp116ComplexPhysicalWalkContourMatrix,
    cmp116ComplexWeakenedPhysicalWalkMatrix] using
    (cmp116Eq214CauchyBoundaryBound_sourceSigmaZeroPi4PhysicalWalkKernel_fixedRate
      (Label := Label) anchor hsourceRange K
      hCker hc hmass hσ h3σκ hμ
      hgeomBase hgeomHead hgeomContinuation
      hrange hbound hK hNR htilt Δ hΔ hΔ1
      left emb radius col.1 row.1 col.2 row.2
      Rweak hRweak hcap hsmall)

/-- Closed fixed-rate bound for one entry of the literal zero-contour patched
covariance matrix.  The estimate is uniform in the ambient torus volume and
retains the source physical distance. -/
theorem norm_sourceSigmaZeroPi4PhysicalWalkContourBaseMatrix_entry_le_fixedRate
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {M Q Nc Rrange NR : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q) (hsourceRange : Rrange + 1 ≤ 4 * M)
    (K : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc)
    {Cker c mass κ σ μ : ℝ}
    (hCker : 0 ≤ Cker) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ) (hμ : 0 < μ)
    (hgeomBase :
      ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-σ) < 1)
    (hgeomHead :
      ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-((κ - σ) - μ)) < 1)
    (hgeomContinuation :
      ((2 ^ 4 : ℕ) : ℝ) *
        Real.exp (-((((κ - σ) - σ) - σ) - μ)) < 1)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist Rrange)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => Cker))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond 4 (M * (2 * Q)),
      (Finset.univ.filter
        (fun y => physicalBondDist x y ≤ Rrange)).card ≤ NR)
    (htilt :
      (Cker + |mass|) *
          (Real.exp (κ * (Rrange : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (Δ : ℕ) (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ) :
    let Dict := cmp116SourceSigmaZeroPi4PhysicalChartDictionary
      (Label := Label) anchor hsourceRange
    let Ahead := cmp99PhysicalPatchHeadWeightedAmplitude c mass
      (cmp99PhysicalBondGeometricRowSum 4 σ)
      (cmp99PhysicalBondGeometricRowSum 4 ((κ - σ) - μ))
    let rho := cmp99PhysicalPatchContinuationWeightedAmplitude
      Cker κ Rrange c mass
      (cmp99PhysicalBondGeometricRowSum 4 σ)
      (cmp99PhysicalBondGeometricRowSum 4
        ((((κ - σ) - σ) - σ) - μ))
    let branching : ℕ :=
      Fintype.card Label * (625 * 626 * Δ ^ 1250)
    ∀ (left : ↥Dict.charts)
      {n : ℕ} (emb : Fin n ↪ FinBox 4 (2 * Q))
      (row col :
        CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (Rweak : ℝ) (hRweak : 1 ≤ Rweak)
      (hsmall :
        (branching : ℝ) * rho * Rweak ^ 10000 < 1),
      ‖cmp116ComplexPhysicalWalkContourBaseMatrix emb
          (fun walk : CMP99AnchoredWalk
              (cmp99PhysicalPatchSuccessorSteps
                Dict.charts Dict.core Dict.enlarged
                physicalBondDist Rrange) left =>
            walk.active Dict.domainActive)
          (fun walk =>
            walk.term
              (cmp99PhysicalPatchHead Dict.charts K
                Dict.enlarged Dict.core hc hmass hK)
              (fun _ => cmp99PhysicalPatchContinuation Dict.charts K
                Dict.enlarged Dict.core hc hmass hK))
          row col‖ ≤
        ((Ahead *
            Real.exp (-(μ *
              (physicalBondDist row.1 col.1 : ℝ))) *
            Rweak ^ 10000) *
          (1 - (branching : ℝ) * rho * Rweak ^ 10000)⁻¹) := by
  dsimp only
  intro left n emb row col Rweak hRweak hsmall
  let Dict := cmp116SourceSigmaZeroPi4PhysicalChartDictionary
    (Label := Label) anchor hsourceRange
  let active := fun walk : CMP99AnchoredWalk
      (cmp99PhysicalPatchSuccessorSteps
        Dict.charts Dict.core Dict.enlarged
        physicalBondDist Rrange) left =>
    walk.active Dict.domainActive
  let term := fun walk : CMP99AnchoredWalk
      (cmp99PhysicalPatchSuccessorSteps
        Dict.charts Dict.core Dict.enlarged
        physicalBondDist Rrange) left =>
    walk.term
      (cmp99PhysicalPatchHead Dict.charts K
        Dict.enlarged Dict.core hc hmass hK)
      (fun _ => cmp99PhysicalPatchContinuation Dict.charts K
        Dict.enlarged Dict.core hc hmass hK)
  obtain ⟨hsummable, hclosed⟩ :=
    tsum_sourceSigmaZeroPi4PhysicalWalkCoefficient_le_fixedRate
      (Label := Label) anchor hsourceRange K
      hCker hc hmass hσ h3σκ hμ
      hgeomBase hgeomHead hgeomContinuation
      hrange hbound hK hNR htilt Δ hΔ hΔ1
      left col.1 row.1 col.2 row.2 Rweak hRweak hsmall
  have hz :
      CMP116Eq214ShiftedPolydisc n (fun _ => 0)
        (0 : Fin n → ℂ) := by
    intro i
    simp
  have hmem :=
    cmp116ComplexWeakeningOfContour_mem_shiftedPolydisc
      emb (fun _ => 0) (0 : Fin n → ℂ) hz
  have hraw :
      ‖cmp116ComplexPhysicalWalkContourBaseMatrix
          emb active term row col‖ ≤
        ∑' walk, Rweak ^ (active walk).card *
          ‖cmp116ComplexPhysicalOperatorCoefficient
            (term walk) col.1 row.1 col.2 row.2‖ := by
    simpa [cmp116ComplexPhysicalWalkContourBaseMatrix,
      cmp116ComplexPhysicalWalkContourMatrix,
      cmp116ComplexWeakenedPhysicalWalkMatrix] using
      (norm_cmp116ComplexWeakenedRandomWalkSeries_le_tsum_majorant
        active
        (fun walk => cmp116ComplexPhysicalOperatorCoefficient
          (term walk) col.1 row.1 col.2 row.2)
        (cmp116ComplexWeakeningOfContour emb (0 : Fin n → ℂ))
        (cmp116ComplexContourRadius emb (fun _ => 0))
        Rweak (zero_le_one.trans hRweak) hmem
        (fun _ d _ => by
          simpa [cmp116ComplexContourRadius] using hRweak)
        hsummable)
  exact hraw.trans hclosed

/-- Volume-uniform `L∞` operator-norm bound for the literal zero-contour
patched covariance matrix.  The physical fixed-rate entry estimate is summed
over the bond metric and the exact `Nc² - 1` Lie-coordinate multiplicity; no
ambient-volume cardinality enters the result. -/
theorem linfty_opNorm_sourceSigmaZeroPi4PhysicalWalkContourBaseMatrix_le_fixedRate
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {M Q Nc Rrange NR : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q) (hsourceRange : Rrange + 1 ≤ 4 * M)
    (K : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc)
    {Cker c mass κ σ μ : ℝ}
    (hCker : 0 ≤ Cker) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ) (hμ : 0 < μ)
    (hgeomBase :
      ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-σ) < 1)
    (hgeomHead :
      ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-((κ - σ) - μ)) < 1)
    (hgeomContinuation :
      ((2 ^ 4 : ℕ) : ℝ) *
        Real.exp (-((((κ - σ) - σ) - σ) - μ)) < 1)
    (hgeomRate :
      ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-μ) < 1)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist Rrange)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => Cker))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond 4 (M * (2 * Q)),
      (Finset.univ.filter
        (fun y => physicalBondDist x y ≤ Rrange)).card ≤ NR)
    (htilt :
      (Cker + |mass|) *
          (Real.exp (κ * (Rrange : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (Δ : ℕ) (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ) :
    let Dict := cmp116SourceSigmaZeroPi4PhysicalChartDictionary
      (Label := Label) anchor hsourceRange
    let Ahead := cmp99PhysicalPatchHeadWeightedAmplitude c mass
      (cmp99PhysicalBondGeometricRowSum 4 σ)
      (cmp99PhysicalBondGeometricRowSum 4 ((κ - σ) - μ))
    let rho := cmp99PhysicalPatchContinuationWeightedAmplitude
      Cker κ Rrange c mass
      (cmp99PhysicalBondGeometricRowSum 4 σ)
      (cmp99PhysicalBondGeometricRowSum 4
        ((((κ - σ) - σ) - σ) - μ))
    let branching : ℕ :=
      Fintype.card Label * (625 * 626 * Δ ^ 1250)
    ∀ (left : ↥Dict.charts)
      {n : ℕ} (emb : Fin n ↪ FinBox 4 (2 * Q))
      (Rweak : ℝ) (hRweak : 1 ≤ Rweak)
      (hsmall :
        (branching : ℝ) * rho * Rweak ^ 10000 < 1),
      ‖cmp116ComplexPhysicalWalkContourBaseMatrix emb
          (fun walk : CMP99AnchoredWalk
              (cmp99PhysicalPatchSuccessorSteps
                Dict.charts Dict.core Dict.enlarged
                physicalBondDist Rrange) left =>
            walk.active Dict.domainActive)
          (fun walk =>
            walk.term
              (cmp99PhysicalPatchHead Dict.charts K
                Dict.enlarged Dict.core hc hmass hK)
              (fun _ => cmp99PhysicalPatchContinuation Dict.charts K
                Dict.enlarged Dict.core hc hmass hK))‖ ≤
        ((Ahead * Rweak ^ 10000) *
            (1 - (branching : ℝ) * rho * Rweak ^ 10000)⁻¹) *
          (((Nc ^ 2 - 1 : ℕ) : ℝ) *
            cmp99PhysicalBondGeometricRowSum 4 μ) := by
  dsimp only
  intro left n emb Rweak hRweak hsmall
  have hAhead :
      0 ≤ cmp99PhysicalPatchHeadWeightedAmplitude c mass
        (cmp99PhysicalBondGeometricRowSum 4 σ)
        (cmp99PhysicalBondGeometricRowSum 4 ((κ - σ) - μ)) := by
    unfold cmp99PhysicalPatchHeadWeightedAmplitude
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg zero_le_two (lt_min hc hmass).le)
        (cmp99PhysicalBondGeometricRowSum_nonneg hgeomBase))
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeomHead)
  have hamplitude :
      0 ≤
        (cmp99PhysicalPatchHeadWeightedAmplitude c mass
            (cmp99PhysicalBondGeometricRowSum 4 σ)
            (cmp99PhysicalBondGeometricRowSum 4 ((κ - σ) - μ)) *
          Rweak ^ 10000) *
        (1 -
          ((Fintype.card Label *
            (625 * 626 * Δ ^ 1250) : ℕ) : ℝ) *
            cmp99PhysicalPatchContinuationWeightedAmplitude
              Cker κ Rrange c mass
              (cmp99PhysicalBondGeometricRowSum 4 σ)
              (cmp99PhysicalBondGeometricRowSum 4
                ((((κ - σ) - σ) - σ) - μ)) *
            Rweak ^ 10000)⁻¹ := by
    exact mul_nonneg
      (mul_nonneg hAhead (pow_nonneg (zero_le_one.trans hRweak) _))
      (inv_nonneg.mpr (sub_pos.mpr hsmall).le)
  apply physicalWalkMatrix_linfty_opNorm_le_of_fixedRate _ _ μ
    hamplitude hgeomRate
  intro row col
  have hentry :=
    norm_sourceSigmaZeroPi4PhysicalWalkContourBaseMatrix_entry_le_fixedRate
      (Label := Label) anchor hsourceRange K
      hCker hc hmass hσ h3σκ hμ
      hgeomBase hgeomHead hgeomContinuation
      hrange hbound hK hNR htilt Δ hΔ hΔ1
      left emb row col Rweak hRweak hsmall
  calc
    ‖cmp116ComplexPhysicalWalkContourBaseMatrix emb
          (fun walk : CMP99AnchoredWalk
              (cmp99PhysicalPatchSuccessorSteps
                (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
                  (Label := Label) anchor hsourceRange).charts
                (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
                  (Label := Label) anchor hsourceRange).core
                (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
                  (Label := Label) anchor hsourceRange).enlarged
                physicalBondDist Rrange) left =>
            walk.active
              (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
                (Label := Label) anchor hsourceRange).domainActive)
          (fun walk =>
            walk.term
              (cmp99PhysicalPatchHead
                (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
                  (Label := Label) anchor hsourceRange).charts K
                (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
                  (Label := Label) anchor hsourceRange).enlarged
                (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
                  (Label := Label) anchor hsourceRange).core hc hmass hK)
              (fun _ => cmp99PhysicalPatchContinuation
                (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
                  (Label := Label) anchor hsourceRange).charts K
                (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
                  (Label := Label) anchor hsourceRange).enlarged
                (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
                  (Label := Label) anchor hsourceRange).core hc hmass hK))
          row col‖ ≤
        ((cmp99PhysicalPatchHeadWeightedAmplitude c mass
              (cmp99PhysicalBondGeometricRowSum 4 σ)
              (cmp99PhysicalBondGeometricRowSum 4 ((κ - σ) - μ)) *
            Real.exp (-(μ *
              (physicalBondDist row.1 col.1 : ℝ))) *
            Rweak ^ 10000) *
          (1 -
            ((Fintype.card Label *
              (625 * 626 * Δ ^ 1250) : ℕ) : ℝ) *
              cmp99PhysicalPatchContinuationWeightedAmplitude
                Cker κ Rrange c mass
                (cmp99PhysicalBondGeometricRowSum 4 σ)
                (cmp99PhysicalBondGeometricRowSum 4
                  ((((κ - σ) - σ) - σ) - μ)) *
              Rweak ^ 10000)⁻¹) := hentry
    _ = ((cmp99PhysicalPatchHeadWeightedAmplitude c mass
              (cmp99PhysicalBondGeometricRowSum 4 σ)
              (cmp99PhysicalBondGeometricRowSum 4 ((κ - σ) - μ)) *
            Rweak ^ 10000) *
          (1 -
            ((Fintype.card Label *
              (625 * 626 * Δ ^ 1250) : ℕ) : ℝ) *
              cmp99PhysicalPatchContinuationWeightedAmplitude
                Cker κ Rrange c mass
                (cmp99PhysicalBondGeometricRowSum 4 σ)
                (cmp99PhysicalBondGeometricRowSum 4
                  ((((κ - σ) - σ) - σ) - μ)) *
              Rweak ^ 10000)⁻¹) *
        Real.exp (-(μ *
          (physicalBondDist row.1 col.1 : ℝ))) := by
      ring

/-- Installing the source patched-parametrix family as the CMP116
covariance exposes the same explicit, volume-uniform `L∞` bound on the
literal `baseCovariance` field.  In particular this theorem does not identify
the covariance walk with the separate contour precision family. -/
theorem sourceSigmaZeroPi4_withPhysicalWalkCovariance_baseCovariance_norm_le
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {M Q Nc Rrange NR n nY : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity n nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (anchor : FinBox 4 Q) (hsourceRange : Rrange + 1 ≤ 4 * M)
    (K : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc)
    {Cker c mass κ σ μ : ℝ}
    (hCker : 0 ≤ Cker) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ) (hμ : 0 < μ)
    (hgeomBase :
      ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-σ) < 1)
    (hgeomHead :
      ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-((κ - σ) - μ)) < 1)
    (hgeomContinuation :
      ((2 ^ 4 : ℕ) : ℝ) *
        Real.exp (-((((κ - σ) - σ) - σ) - μ)) < 1)
    (hgeomRate :
      ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-μ) < 1)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist Rrange)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => Cker))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond 4 (M * (2 * Q)),
      (Finset.univ.filter
        (fun y => physicalBondDist x y ≤ Rrange)).card ≤ NR)
    (htilt :
      (Cker + |mass|) *
          (Real.exp (κ * (Rrange : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (Δ : ℕ) (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ) :
    let Dict := cmp116SourceSigmaZeroPi4PhysicalChartDictionary
      (Label := Label) anchor hsourceRange
    let Ahead := cmp99PhysicalPatchHeadWeightedAmplitude c mass
      (cmp99PhysicalBondGeometricRowSum 4 σ)
      (cmp99PhysicalBondGeometricRowSum 4 ((κ - σ) - μ))
    let rho := cmp99PhysicalPatchContinuationWeightedAmplitude
      Cker κ Rrange c mass
      (cmp99PhysicalBondGeometricRowSum 4 σ)
      (cmp99PhysicalBondGeometricRowSum 4
        ((((κ - σ) - σ) - σ) - μ))
    let branching : ℕ :=
      Fintype.card Label * (625 * 626 * Δ ^ 1250)
    ∀ (left : ↥Dict.charts)
      (emb : Fin n ↪ FinBox 4 (2 * Q))
      (Rweak : ℝ) (hRweak : 1 ≤ Rweak)
      (hsmall :
        (branching : ℝ) * rho * Rweak ^ 10000 < 1)
      (psi : RestrictedField C.spectatorSupport Psi)
      (phi : RestrictedField C.fluctuationSupport Phi),
      ‖(C.withComplexPhysicalWalkCovariance emb
          (fun walk : CMP99AnchoredWalk
              (cmp99PhysicalPatchSuccessorSteps
                Dict.charts Dict.core Dict.enlarged
                physicalBondDist Rrange) left =>
            walk.active Dict.domainActive)
          (fun _ _ walk =>
            walk.term
              (cmp99PhysicalPatchHead Dict.charts K
                Dict.enlarged Dict.core hc hmass hK)
              (fun _ => cmp99PhysicalPatchContinuation Dict.charts K
                Dict.enlarged Dict.core hc hmass hK))
        ).baseCovariance psi phi‖ ≤
        ((Ahead * Rweak ^ 10000) *
            (1 - (branching : ℝ) * rho * Rweak ^ 10000)⁻¹) *
          (((Nc ^ 2 - 1 : ℕ) : ℝ) *
            cmp99PhysicalBondGeometricRowSum 4 μ) := by
  dsimp only
  intro left emb Rweak hRweak hsmall psi phi
  simpa only [
    CMP116Eq214PhysicalContourDensity.withComplexPhysicalWalkCovariance_baseCovariance]
    using
      (linfty_opNorm_sourceSigmaZeroPi4PhysicalWalkContourBaseMatrix_le_fixedRate
        (Label := Label) anchor hsourceRange K
        hCker hc hmass hσ h3σκ hμ
        hgeomBase hgeomHead hgeomContinuation hgeomRate
        hrange hbound hK hNR htilt Δ hΔ hΔ1
        left emb Rweak hRweak hsmall)

end

end YangMills.RG
