/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatRetainedPhysicalTower
import YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime

/-!
PRE-VALIDATION: source present; `.olean` not yet materialized and these
declarations have not yet been verified by the Lean compiler.

# The retained terminal prefix is the generated `Q'` tower

The retained physical construction and the typed active-region-chain
construction recurse through the same physical `Ubar` backgrounds and the
same transported one-step averages.  This file identifies the last retained
prefix with the already-consumed generated `weightedQprimeTower`; it does not
introduce a second family of `Q'` operators or an equality supplied by a
caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The last prefix retained by the physical recursive constructor is
literally the tower generated on the canonical typed active-region chain. -/
theorem cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) :
    ∀ (depth : ℕ) (spacing epsilon : ℝ)
      (background : GaugeConfig d
        (cmp99RegionalLatticeSize M N depth) (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d
        (cmp99RegionalLatticeSize M N depth),
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      (cmp99SourceGeneratedRetainedPhysicalTower hd hM rho Omega depth
        spacing epsilon background chain fineSmall).towerAt (Fin.last depth) =
        (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
          |>.weightedQprimeTower hd hM rho spacing epsilon background chain
            fineSmall) := by
  intro depth
  induction depth with
  | zero =>
      intro spacing epsilon background chain fineSmall
      rfl
  | succ depth ih =>
      intro spacing epsilon background chain fineSmall
      let Scale : CMP99SourceNormalizedRegionalScale
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
          background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
          background
          (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
          epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d
          (cmp99RegionalLatticeSize M N depth),
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
            background (cmp99SourceBlockAverageWeight M d) epsilon
            chain.epsilon_nonneg chain.head_noWinding chain.head_logSmall
            fineSmall e
      let Tail := cmp99SourceGeneratedRetainedPhysicalTower hd hM rho Omega
        depth ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      have hregion :
          cmp99ActiveCoarseRegion
              (M := M) (N' := cmp99RegionalLatticeSize M N depth)
              (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =
            cmp99IteratedLiftActiveRegion (M := M) Omega depth :=
        cmp99ActiveCoarseRegion_iteratedLift_succ_eq (M := M) Omega depth
      let Tail' : CMP99SourceRetainedPhysicalTower rho
          (cmp99ActiveCoarseRegion
            (M := M) (N' := cmp99RegionalLatticeSize M N depth)
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
          M ((M : ℝ) * spacing)
          Scale.toSourceScale.data.nextBackground depth :=
        hregion.symm ▸ Tail
      let regions :=
        cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
      let regions' : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion
            (M := M) (N' := cmp99RegionalLatticeSize M N depth)
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
          depth := by
        rw [hregion]
        exact regions
      have htail := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      have htail' :
          Tail'.towerAt (Fin.last depth) =
            regions'.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              Scale.toSourceScale.data.nextBackground chain.tail nextSmall := by
        simpa [Tail', regions', regions] using htail
      simpa [cmp99SourceGeneratedRetainedPhysicalTower,
        cmp99SourceIteratedLiftActiveRegionChain,
        CMP99SourceActiveRegionChain.weightedQprimeTower, Scale, Tail',
        regions'] using
        congrArg
          (fun T => CMP99SourceWeightedRegionalTower.step
            (g := SUNLieCoord Nc)
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
            (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
            spacing
            (cmp99SourceWeightedPhysicalTransport rho background) T)
          htail'

/-- At the literal flat background, the terminal retained prefix is therefore
the canonical generated `Q'` tower used by the CMP99 transition, mass,
precision, and covariance consumers. -/
theorem cmp99SourceFlatRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) (spacing : ℝ) :
    (cmp99SourceFlatRetainedPhysicalTower hd hM rho Omega depth spacing).towerAt
        (Fin.last depth) =
      (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
        |>.weightedQprimeTower hd hM rho spacing 0
          (cmp99SourceFlatGaugeConfig d
            (cmp99RegionalLatticeSize M N depth) Nc)
          (cmp99SourceFlatZeroRadiusChain depth)
          (by
            intro e
            change ‖((1 : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0
            simp)) := by
  exact
    cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower
      hd hM rho Omega depth spacing 0
      (cmp99SourceFlatGaugeConfig d
        (cmp99RegionalLatticeSize M N depth) Nc)
      (cmp99SourceFlatZeroRadiusChain depth) _

end

end YangMills.RG
