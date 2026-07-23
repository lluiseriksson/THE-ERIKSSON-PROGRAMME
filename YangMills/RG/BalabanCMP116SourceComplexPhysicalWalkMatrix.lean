/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexPhysicalWalkMatrix
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

end

end YangMills.RG
