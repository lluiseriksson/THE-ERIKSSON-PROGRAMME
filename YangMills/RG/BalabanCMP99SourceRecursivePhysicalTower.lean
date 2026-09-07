/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceUbarSmallFieldPropagation
import YangMills.RG.BalabanCMP99SourceWeightedPhysicalTower
import YangMills.RG.BalabanCMP99SourceRegionalLiftTower

/-!
# A recursively generated physical CMP99 source tower

The caller supplies one fine background and a scalar admissibility schedule.
Every subsequent background is the literal `Ubar` of the preceding scale;
its linkwise smallness is proved rather than requested.  The active regions
are the canonical complete-block lifts, so coarsening matches the dependent
tail type exactly.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Purely scalar conditions needed to iterate the source `Ubar` map.  This
contains no background fields and no linkwise estimates. -/
inductive CMP99SourceUbarRadiusChain (d M Nc : ℕ)
    [NeZero d] [NeZero M] [NeZero Nc] : ℕ → ℝ → Prop
  | stop (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) :
      CMP99SourceUbarRadiusChain d M Nc 0 epsilon
  | step {depth : ℕ} (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon)
      (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilon <
        cmp99UbarNoWindingThreshold Nc)
      (logSmall :
        cmp99UbarLogRadius
            (cmp99SourceUbarFineNoWindingBudget
              (d := d) (M := M) (Nc := Nc) epsilon noWinding) < 1)
      (tail : CMP99SourceUbarRadiusChain d M Nc depth
        (cmp99SourceUbarNextFineRadius d M epsilon)) :
      CMP99SourceUbarRadiusChain d M Nc (depth + 1) epsilon

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- A scalar chain and one initial small-field certificate produce a complete
background-faithful tower.  In particular, no tail background and no tail
smallness proof occur in the public interface. -/
theorem nonempty_cmp99SourceRecursivePhysicalTower
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) :
    ∀ (depth : ℕ) (spacing epsilon : ℝ)
      (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc)),
      CMP99SourceUbarRadiusChain d M Nc depth epsilon →
      (∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
      Nonempty (CMP99SourceWeightedPhysicalTower rho
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
        spacing background) := by
  intro depth
  induction depth with
  | zero =>
      intro spacing epsilon background _chain _fineSmall
      exact ⟨CMP99SourceWeightedPhysicalTower.stop rho Omega spacing background⟩
  | succ depth ih =>
      intro spacing epsilon background chain fineSmall
      cases chain with
      | step _ epsilon_nonneg noWinding logSmall tailChain =>
          let Scale : CMP99SourceNormalizedRegionalScale
              (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
              background :=
            CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM
              (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
              background
              (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
              epsilon epsilon_nonneg noWinding fineSmall
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
                epsilon_nonneg noWinding logSmall fineSmall e
          obtain ⟨Tail⟩ := ih ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground tailChain nextSmall
          have Tail' : CMP99SourceWeightedPhysicalTower rho
              (cmp99ActiveCoarseRegion
                (M := M) (N' := cmp99RegionalLatticeSize M N depth)
                (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
              ((M : ℝ) * spacing)
              Scale.toSourceScale.data.nextBackground := by
            rw [cmp99ActiveCoarseRegion_iteratedLift_succ_eq]
            exact Tail
          exact ⟨CMP99SourceWeightedPhysicalTower.step rho
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
            spacing background Scale Tail'⟩

/-- Canonical choice of the recursively generated source tower. -/
noncomputable def cmp99SourceRecursivePhysicalTower
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    CMP99SourceWeightedPhysicalTower rho
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
      spacing background :=
  Classical.choice
    (nonempty_cmp99SourceRecursivePhysicalTower hd hM rho Omega depth spacing
      epsilon background chain fineSmall)

/-- The recursively generated tower inherits the exact source normalization
identity at every depth. -/
theorem cmp99SourceRecursivePhysicalTower_Qprime_comp_weightedAdjoint_eq_Cj
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let T := cmp99SourceRecursivePhysicalTower hd hM rho Omega depth spacing
      epsilon background chain fineSmall
    T.toWeightedTower.Qprime.comp T.toWeightedTower.weightedAdjoint =
      cmp99SourceTowerNormalization T.toWeightedTower.depth •
        ContinuousLinearMap.id ℝ T.toWeightedTower.TerminalSpace.carrier := by
  dsimp only
  exact CMP99SourceWeightedPhysicalTower.Qprime_comp_weightedAdjoint_eq_Cj _

end

end YangMills.RG
