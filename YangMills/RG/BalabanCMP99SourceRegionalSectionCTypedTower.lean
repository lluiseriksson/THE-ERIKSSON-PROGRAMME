/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalSectionCTypedWalk
import YangMills.RG.BalabanCMP99SourceRegionalSectionCWeightedRow
import YangMills.RG.DependentFinitePiLpWeightedRowWalk

/-!
# The full scale-typed CMP99 Section C tower

The `j+1` consecutive factors of (3.97) act on the genuine nested regional
carriers `Omega_0, ..., Omega_{j+1}`.  This file constructs their complete
dependent product and proves a fixed-rate weighted-row estimate.  No regional
carrier is replaced by an ambient endomorphism space.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- Coarse site family on the literal source region sequence. -/
abbrev CMP99OmegaRegionalCoarseSiteFamily
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :=
  ActiveGaugeRegion.Site
    (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r))

/-- One physical distance family for every pair of regional scale carriers. -/
def cmp99OmegaRegionalCoarseCrossDist
    (Seq : CMP99SourceOmegaGeometry cell j) (r s : Fin (j + 2))
    (target : CMP99OmegaRegionalCoarseSiteFamily (M := M) Seq s)
    (source : CMP99OmegaRegionalCoarseSiteFamily (M := M) Seq r) : ℕ :=
  finBoxDist
    (cmp99OmegaCoarseRepresentative (M := M) Seq s target)
    (cmp99OmegaCoarseRepresentative (M := M) Seq r source)

@[simp] theorem cmp99OmegaRegionalCoarseCrossDist_self
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (x : CMP99OmegaRegionalCoarseSiteFamily (M := M) Seq r) :
    cmp99OmegaRegionalCoarseCrossDist (M := M) Seq r r x x = 0 :=
  finBoxDist_self _

theorem cmp99OmegaRegionalCoarseCrossDist_triangle
    (Seq : CMP99SourceOmegaGeometry cell j) (r s t : Fin (j + 2))
    (target : CMP99OmegaRegionalCoarseSiteFamily (M := M) Seq t)
    (middle : CMP99OmegaRegionalCoarseSiteFamily (M := M) Seq s)
    (source : CMP99OmegaRegionalCoarseSiteFamily (M := M) Seq r) :
    cmp99OmegaRegionalCoarseCrossDist (M := M) Seq r t target source ≤
      cmp99OmegaRegionalCoarseCrossDist (M := M) Seq s t target middle +
        cmp99OmegaRegionalCoarseCrossDist (M := M) Seq r s middle source :=
  finBoxDist_triangle _ _ _

/-- On consecutive indices, the global cross-scale metric is literally the
native transition metric used by the one-step factor. -/
theorem cmp99OmegaRegionalCoarseCrossDist_transition
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    cmp99OmegaRegionalCoarseCrossDist (M := M) Seq r.castSucc r.succ =
      cmp99OmegaCoarseTransitionDist (M := M) Seq r :=
  rfl

/-- The `r`-th literal cut factor, typed as one arrow in the full tower. -/
noncomputable def cmp99OmegaSourceSectionCCutTowerStep
    (Seq : CMP99SourceOmegaGeometry cell j)
    (Cuts : ∀ r : Fin (j + 1),
      CMP99SourceSectionCTransitionCutData (M := M) Seq r)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (r : Fin (j + 1)) :
    DependentFinitePiLpArrow
      (CMP99OmegaRegionalCoarseSiteFamily (M := M) Seq)
      (SUNLieCoord Nc) r.castSucc r.succ :=
  cmp99OmegaSourcePhysicalOneStepSectionCCutFactor
    Seq r (Cuts r) rho U hspacing ha

/-- Full source-ordered Section C walk from `Omega_0` to `Omega_{j+1}`. -/
noncomputable def cmp99OmegaSourceSectionCCutFactorTower
    (Seq : CMP99SourceOmegaGeometry cell j)
    (Cuts : ∀ r : Fin (j + 1),
      CMP99SourceSectionCTransitionCutData (M := M) Seq r)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :=
  DependentArrowWalk.finSuccPath
    (cmp99OmegaSourceSectionCCutTowerStep
      Seq Cuts rho U hspacing ha)

/-- The tower contains exactly the printed `j+1` consecutive transitions. -/
@[simp] theorem cmp99OmegaSourceSectionCCutFactorTower_length
    (Seq : CMP99SourceOmegaGeometry cell j)
    (Cuts : ∀ r : Fin (j + 1),
      CMP99SourceSectionCTransitionCutData (M := M) Seq r)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    (cmp99OmegaSourceSectionCCutFactorTower
      Seq Cuts rho U hspacing ha).length = j + 1 := by
  simp [cmp99OmegaSourceSectionCCutFactorTower]

set_option maxHeartbeats 2400000 in
/-- The complete typed Section C tower has product amplitude and one unchanged
weighted-row decay rate, uniformly in the ambient volume. -/
theorem cmp99OmegaSourceSectionCCutFactorTower_weightedRowKernelBound
    (Seq : CMP99SourceOmegaGeometry cell j)
    (Cuts : ∀ r : Fin (j + 1),
      CMP99SourceSectionCTransitionCutData (M := M) Seq r)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    let walk := cmp99OmegaSourceSectionCCutFactorTower
      Seq Cuts rho U hspacing ha
    FinitePiLpTypedWeightedRowKernelBound
      (dependentFinitePiLpWalkOperator
        (CMP99OmegaRegionalCoarseSiteFamily (M := M) Seq)
        (SUNLieCoord Nc) walk)
      (cmp99OmegaRegionalCoarseCrossDist (M := M) Seq
        (cmp99OmegaZeroIndex j) (cmp99OmegaLastIndex j))
      ((cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowAmplitude
        M spacing a) ^ (j + 1))
      (cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate
        M spacing a) := by
  dsimp only
  let Site := CMP99OmegaRegionalCoarseSiteFamily (M := M) Seq
  let dist := cmp99OmegaRegionalCoarseCrossDist (M := M) Seq
  let step := cmp99OmegaSourceSectionCCutTowerStep
    Seq Cuts rho U hspacing ha
  let A := cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowAmplitude
    M spacing a
  let rate := cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate
    M spacing a
  have hrate : 0 ≤ rate :=
    (cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate_pos
      (M := M) hspacing ha).le
  have hstep : ∀ r,
      FinitePiLpTypedWeightedRowKernelBound
        (step r) (dist r.castSucc r.succ) A rate := by
    intro r
    simpa [step, dist, A, rate,
      cmp99OmegaRegionalCoarseCrossDist_transition] using
      cmp99OmegaSourcePhysicalOneStepSectionCCutFactor_weightedRowKernelBound
        Seq r (Cuts r) rho U hspacing ha
  have hfull :=
    dependentFinitePiLpWalkOperator_finSuccPath_weightedRowKernelBound
      Site (SUNLieCoord Nc) dist
      (fun r x => cmp99OmegaRegionalCoarseCrossDist_self
        (M := M) Seq r x)
      (fun r s t target middle source =>
        cmp99OmegaRegionalCoarseCrossDist_triangle
          (M := M) Seq r s t target middle source)
      step (fun _ => A) hrate hstep
  simpa [Site, dist, step, A, rate,
    cmp99OmegaSourceSectionCCutFactorTower,
    cmp99OmegaZeroIndex, cmp99OmegaLastIndex] using hfull

end

end YangMills.RG
