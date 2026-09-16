/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99MultiscaleAverage
import YangMills.RG.BalabanCMP99SourceRegionalAdjoint

/-!
# A regional tower of physical one-scale CMP99 averages

This file instantiates the abstract varying spaces of `Q'_j` by the actual
active regional zero-cochain spaces.  Every nonterminal node is constructed
from:

* a fine region made of complete blocks;
* its literal complete-block coarse region;
* a group-valued gauge background on the fine lattice;
* the certified block-contained contour holonomy in that background;
* the resulting physical adjoint block average.

Thus no `E_k` or `Q_k` is supplied as an arbitrary continuous linear map.
The remaining source obligation is intentionally visible: the backgrounds at
successive nodes are typed gauge configurations, but this module does not
claim that the coarse background is produced from the fine one by Balaban's
nonlinear `Ubar`.  The existing `Ubar.lean` currently lands in a represented
algebra rather than in a group-valued `GaugeConfig`, so treating it as that
producer would be type- and source-incorrect.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d Nc : ℕ} [NeZero d] [NeZero Nc]

/-- A bundled real Hilbert space.  The terminal lattice and region vary with
the number of physical averaging steps, so the analytic instances travel with
the terminal carrier. -/
structure CMP99TowerHilbertSpace where
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℝ carrier]
  [completeSpace : CompleteSpace carrier]

attribute [instance] CMP99TowerHilbertSpace.normedAddCommGroup
attribute [instance] CMP99TowerHilbertSpace.innerProductSpace
attribute [instance] CMP99TowerHilbertSpace.completeSpace

/-- A certified finite chain of regional physical averages.  The fields are
not free inputs: the only public constructors below are `stop` and `step`, and
`step` builds `Qprime` from the literal physical one-scale average.  Bundling
the terminal carrier avoids irrelevant dependent transports between different
proofs that intermediate lattice sizes are nonzero. -/
structure CMP99RegionalAverageTower (rho : SUNAdjointModel Nc)
    {N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion d N) where
  depth : ℕ
  TerminalSpace : CMP99TowerHilbertSpace
  Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
    TerminalSpace.carrier
  normalization : ℝ
  Qprime_comp_adjoint :
    Qprime.comp Qprime.adjoint =
      normalization • ContinuousLinearMap.id ℝ TerminalSpace.carrier

/-- The zero-step tower on a regional field space. -/
noncomputable def CMP99RegionalAverageTower.stop
    (rho : SUNAdjointModel Nc) {N : ℕ} [NeZero N]
    (Omega : ActiveGaugeRegion d N) :
    CMP99RegionalAverageTower rho Omega where
  depth := 0
  TerminalSpace :=
    { carrier := ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) }
  Qprime := ContinuousLinearMap.id ℝ
    (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
  normalization := 1
  Qprime_comp_adjoint := by
    ext eta
    simp

/-- The literal physical one-scale factor stored at the head of a nonterminal
tower. -/
noncomputable def cmp99RegionalAverageTowerStep
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N')) (w : ℝ)
    (background : GaugeConfig d (M * N') (SUN Nc)) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (SUNLieCoord Nc) :=
  cmp99AdjointBlockAverageCLM Omega w rho
    (cmp99ContourHolonomy
      (cmp99BlockContainedContourSystem (G := SUN Nc)) background)

/-- Exact one-scale normalization for the concrete factor used in the tower. -/
theorem cmp99RegionalAverageTowerStep_comp_adjoint
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (w : ℝ) (background : GaugeConfig d (M * N') (SUN Nc)) :
    (cmp99RegionalAverageTowerStep rho Omega w background).comp
        (cmp99RegionalAverageTowerStep rho Omega w background).adjoint =
      (w ^ 2 * (M : ℝ) ^ d) •
        ContinuousLinearMap.id ℝ
          (ActiveGaugeZeroCochain
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
          (SUNLieCoord Nc)) := by
  change (cmp99AdjointBlockAverageCLM Omega w rho
      (cmp99ContourHolonomy
        (cmp99BlockContainedContourSystem (G := SUN Nc)) background)).comp
      (cmp99AdjointBlockAverageCLM Omega w rho
        (cmp99ContourHolonomy
          (cmp99BlockContainedContourSystem (G := SUN Nc)) background)).adjoint = _
  rw [← cmp99AdjointBlockSynthesisCLM_eq_adjoint Omega hOmega w rho
    (cmp99ContourHolonomy
      (cmp99BlockContainedContourSystem (G := SUN Nc)) background)]
  exact cmp99AdjointBlockAverage_comp_synthesis Omega hOmega w rho
    (cmp99ContourHolonomy
      (cmp99BlockContainedContourSystem (G := SUN Nc)) background)

/-- Add one actual physical regional average to a certified tail.  The tail
starts on the literal complete-block coarse region, hence saturation is
required at every scale at which `step` is called. -/
noncomputable def CMP99RegionalAverageTower.step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (w : ℝ) (background : GaugeConfig d (M * N') (SUN Nc))
    (tail : CMP99RegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    CMP99RegionalAverageTower rho Omega where
  depth := tail.depth + 1
  TerminalSpace := tail.TerminalSpace
  Qprime := tail.Qprime.comp
    (cmp99RegionalAverageTowerStep rho Omega w background)
  normalization := (w ^ 2 * (M : ℝ) ^ d) * tail.normalization
  Qprime_comp_adjoint := by
    let Q := cmp99RegionalAverageTowerStep rho Omega w background
    ext eta
    rw [ContinuousLinearMap.adjoint_comp]
    change tail.Qprime
        (Q (Q.adjoint (tail.Qprime.adjoint eta))) =
      ((w ^ 2 * (M : ℝ) ^ d) * tail.normalization) • eta
    have hQ := congrArg
      (fun A : ActiveGaugeZeroCochain
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
          (SUNLieCoord Nc) →L[ℝ]
          ActiveGaugeZeroCochain
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
            (SUNLieCoord Nc) => A (tail.Qprime.adjoint eta))
      (cmp99RegionalAverageTowerStep_comp_adjoint
        rho Omega hOmega w background)
    change Q (Q.adjoint (tail.Qprime.adjoint eta)) =
      (w ^ 2 * (M : ℝ) ^ d) • tail.Qprime.adjoint eta at hQ
    rw [hQ, map_smul]
    have htail := congrArg
      (fun A : tail.TerminalSpace.carrier →L[ℝ]
        tail.TerminalSpace.carrier => A eta)
      tail.Qprime_comp_adjoint
    change tail.Qprime (tail.Qprime.adjoint eta) =
      tail.normalization • eta at htail
    rw [htail, smul_smul]

@[simp] theorem CMP99RegionalAverageTower.depth_stop
    (rho : SUNAdjointModel Nc) {N : ℕ} [NeZero N]
    (Omega : ActiveGaugeRegion d N) :
    (CMP99RegionalAverageTower.stop rho Omega).depth = 0 :=
  rfl

@[simp] theorem CMP99RegionalAverageTower.normalization_stop
    (rho : SUNAdjointModel Nc) {N : ℕ} [NeZero N]
    (Omega : ActiveGaugeRegion d N) :
    (CMP99RegionalAverageTower.stop rho Omega).normalization = 1 :=
  rfl

@[simp] theorem CMP99RegionalAverageTower.Qprime_stop
    (rho : SUNAdjointModel Nc) {N : ℕ} [NeZero N]
    (Omega : ActiveGaugeRegion d N) :
    (CMP99RegionalAverageTower.stop rho Omega).Qprime =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :=
  rfl

theorem CMP99RegionalAverageTower.depth_step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (w : ℝ) (background : GaugeConfig d (M * N') (SUN Nc))
    (tail : CMP99RegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    (CMP99RegionalAverageTower.step rho Omega hOmega w background tail).depth =
      tail.depth + 1 :=
  rfl

theorem CMP99RegionalAverageTower.normalization_step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (w : ℝ) (background : GaugeConfig d (M * N') (SUN Nc))
    (tail : CMP99RegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    (CMP99RegionalAverageTower.step rho Omega hOmega w background tail).normalization =
      (w ^ 2 * (M : ℝ) ^ d) * tail.normalization :=
  rfl

theorem CMP99RegionalAverageTower.Qprime_step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (w : ℝ) (background : GaugeConfig d (M * N') (SUN Nc))
    (tail : CMP99RegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    (CMP99RegionalAverageTower.step rho Omega hOmega w background tail).Qprime =
      tail.Qprime.comp
        (cmp99RegionalAverageTowerStep rho Omega w background) :=
  rfl

/-- Pointwise terminal normalization, available for every tower constructed by
the certified `stop`/`step` interface. -/
theorem CMP99RegionalAverageTower.Qprime_comp_adjoint_apply
    {rho : SUNAdjointModel Nc}
    {N : ℕ} [NeZero N] {Omega : ActiveGaugeRegion d N}
    (T : CMP99RegionalAverageTower rho Omega)
    (eta : T.TerminalSpace.carrier) :
    T.Qprime (T.Qprime.adjoint eta) = T.normalization • eta := by
  have h := congrArg
    (fun A : T.TerminalSpace.carrier →L[ℝ]
      T.TerminalSpace.carrier => A eta)
    T.Qprime_comp_adjoint
  simpa using h

end

end YangMills.RG
