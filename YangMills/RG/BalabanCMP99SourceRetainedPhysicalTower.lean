/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRecursivePhysicalTower

/-!
# Retain every physical prefix of the CMP99 source tower

The terminal tower used by one scale does not by itself expose all operators
`Q'_r` required simultaneously in CMP99 (3.24).  This file constructs one
source-faithful object from the same recursive `Ubar` chain and retains every
prefix on the original fine field.  The constructor is private: callers
cannot supply an unrelated family of averages.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- All prefixes of one physical source tower, indexed from the identity
prefix through the terminal prefix.  Every member acts on the same original
fine field. -/
structure CMP99SourceRetainedPhysicalTower
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) (M : ℕ) (spacing : ℝ)
    (background : GaugeConfig d N (SUN Nc)) (depth : ℕ) where
  private mk ::
  towerAt : Fin (depth + 1) →
    CMP99SourceWeightedRegionalTower
      (g := SUNLieCoord Nc) Omega spacing
  towerAt_depth : ∀ r, (towerAt r).depth = r.val
  towerAt_terminalSpacing : ∀ r,
    (towerAt r).terminalSpacing = (M : ℝ) ^ r.val * spacing
  /-- The zeroth retained prefix is literally the empty composition. -/
  towerAt_zero : towerAt 0 =
    CMP99SourceWeightedRegionalTower.stop
      (g := SUNLieCoord Nc) Omega spacing
  /-- The literal next scale average between consecutive retained prefix
  carriers. -/
  nextAverage : ∀ k : Fin depth,
    (towerAt k.castSucc).TerminalSpace.carrier →L[ℝ]
      (towerAt k.succ).TerminalSpace.carrier
  /-- Exact printed order `Q'_(k+1) = Q_k(U_k) Q'_k`.  Storing this in the
  retained object prevents a family of unrelated normalized prefixes from
  satisfying the public interface. -/
  towerAt_succ_Qprime : ∀ k : Fin depth,
    (towerAt k.succ).Qprime =
      (nextAverage k).comp (towerAt k.castSucc).Qprime
  /-- The literal site type on which the terminal field of each retained
  prefix lives.  This prevents downstream code from supplying a second,
  unrelated scale-lattice dictionary. -/
  levelSite : Fin (depth + 1) → Type
  [levelSiteDecidableEq : ∀ r, DecidableEq (levelSite r)]
  [levelSiteFintype : ∀ r, Fintype (levelSite r)]
  /-- Literal identification of each otherwise bundled terminal carrier with
  its recursively generated scale field.  Type equality is stronger than a
  caller-chosen isometry and makes the downstream dictionary canonical. -/
  levelCarrierEq : ∀ r,
    (towerAt r).TerminalSpace.carrier =
      PiLp 2 (fun _ : levelSite r => SUNLieCoord Nc)
  /-- The norm-preserving realization accompanying the literal carrier
  equality.  It is generated only by the private recursive constructor. -/
  levelEquiv : ∀ r,
    (towerAt r).TerminalSpace.carrier ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : levelSite r => SUNLieCoord Nc)

attribute [instance]
  CMP99SourceRetainedPhysicalTower.levelSiteDecidableEq
  CMP99SourceRetainedPhysicalTower.levelSiteFintype

/-- The retained family is nonempty for the literal recursively generated
`Ubar` chain.  No coarse backgrounds or prefix operators are caller inputs. -/
theorem nonempty_cmp99SourceRetainedPhysicalTower
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) :
    ∀ (depth : ℕ) (spacing epsilon : ℝ)
      (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc)),
      CMP99SourceUbarRadiusChain d M Nc depth epsilon →
      (∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
      Nonempty (CMP99SourceRetainedPhysicalTower rho
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
        M spacing background depth) := by
  intro depth
  induction depth with
  | zero =>
      intro spacing epsilon background _chain _fineSmall
      refine ⟨CMP99SourceRetainedPhysicalTower.mk
        (fun _ => CMP99SourceWeightedRegionalTower.stop
          (g := SUNLieCoord Nc) Omega spacing) ?_ ?_
        rfl
        (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)
        (fun _ => ActiveGaugeRegion.Site Omega)
        (fun _ => rfl)
        (fun _ => LinearIsometryEquiv.refl ℝ _)⟩
      · intro r
        have hr : r = 0 := Fin.eq_zero r
        subst r
        rfl
      · intro r
        have hr : r = 0 := Fin.eq_zero r
        subst r
        change spacing = (M : ℝ) ^ 0 * spacing
        simp
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
          have hregion :
              cmp99ActiveCoarseRegion
                  (M := M) (N' := cmp99RegionalLatticeSize M N depth)
                  (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =
                cmp99IteratedLiftActiveRegion (M := M) Omega depth :=
            cmp99ActiveCoarseRegion_iteratedLift_succ_eq
              (M := M) Omega depth
          have Tail' : CMP99SourceRetainedPhysicalTower rho
              (cmp99ActiveCoarseRegion
                (M := M) (N' := cmp99RegionalLatticeSize M N depth)
                (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
              M ((M : ℝ) * spacing)
              Scale.toSourceScale.data.nextBackground depth := by
            rw [hregion]
            exact Tail
          let headPrefix := CMP99SourceWeightedRegionalTower.stop
            (g := SUNLieCoord Nc)
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) spacing
          let succPrefix (r : Fin (depth + 1)) :=
            CMP99SourceWeightedRegionalTower.step
              (g := SUNLieCoord Nc)
              (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
              (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
              spacing
              (cmp99SourceWeightedPhysicalTransport rho background)
              (Tail'.towerAt r)
          let prefixTower : Fin (depth + 2) →
              CMP99SourceWeightedRegionalTower
                (g := SUNLieCoord Nc)
                (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
                spacing :=
            Fin.cases headPrefix succPrefix
          let prefixNextAverage : ∀ k : Fin (depth + 1),
              (prefixTower k.castSucc).TerminalSpace.carrier →L[ℝ]
                (prefixTower k.succ).TerminalSpace.carrier := by
            intro k
            refine Fin.cases (motive := fun k : Fin (depth + 1) =>
              (prefixTower k.castSucc).TerminalSpace.carrier →L[ℝ]
                (prefixTower k.succ).TerminalSpace.carrier)
              ?_ (fun s => ?_) k
            · exact (Tail'.towerAt 0).Qprime.comp
                (cmp99SourceTransportedBlockAverageCLM
                  (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
                  (cmp99SourceWeightedPhysicalTransport rho background))
            · exact Tail'.nextAverage s
          let prefixQprimeSucc : ∀ k : Fin (depth + 1),
              (prefixTower k.succ).Qprime =
                (prefixNextAverage k).comp
                  (prefixTower k.castSucc).Qprime := by
            intro k
            refine Fin.cases (motive := fun k : Fin (depth + 1) =>
              (prefixTower k.succ).Qprime =
                (prefixNextAverage k).comp
                  (prefixTower k.castSucc).Qprime)
              ?_ (fun s => ?_) k
            · change (Tail'.towerAt 0).Qprime.comp
                  (cmp99SourceTransportedBlockAverageCLM
                    (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
                    (cmp99SourceWeightedPhysicalTransport rho background)) =
                (prefixNextAverage 0).comp
                  (ContinuousLinearMap.id ℝ _)
              simp only [prefixNextAverage, prefixTower, Fin.cases_zero]
              rw [ContinuousLinearMap.comp_id]
              rfl
            · change (Tail'.towerAt s.succ).Qprime.comp
                  (cmp99SourceTransportedBlockAverageCLM
                    (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
                    (cmp99SourceWeightedPhysicalTransport rho background)) =
                (Tail'.nextAverage s).comp
                  ((Tail'.towerAt s.castSucc).Qprime.comp
                    (cmp99SourceTransportedBlockAverageCLM
                      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
                      (cmp99SourceWeightedPhysicalTransport rho background)))
              rw [← ContinuousLinearMap.comp_assoc,
                Tail'.towerAt_succ_Qprime s]
          let prefixSite : Fin (depth + 2) → Type :=
            Fin.cases
              (ActiveGaugeRegion.Site
                (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
              (fun r => Tail'.levelSite r)
          let prefixSiteDecidableEq : ∀ r, DecidableEq (prefixSite r) := by
            intro r
            refine Fin.cases ?_ (fun j => ?_) r
            · change DecidableEq (ActiveGaugeRegion.Site
                (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
              exact inferInstance
            · exact Tail'.levelSiteDecidableEq j
          let prefixSiteFintype : ∀ r, Fintype (prefixSite r) := by
            intro r
            refine Fin.cases ?_ (fun j => ?_) r
            · change Fintype (ActiveGaugeRegion.Site
                (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
              exact inferInstance
            · exact Tail'.levelSiteFintype j
          letI : ∀ r, DecidableEq (prefixSite r) := prefixSiteDecidableEq
          letI : ∀ r, Fintype (prefixSite r) := prefixSiteFintype
          let prefixCarrierEq : ∀ r : Fin (depth + 2),
              (prefixTower r).TerminalSpace.carrier =
                PiLp 2 (fun _ : prefixSite r => SUNLieCoord Nc) := by
            intro r
            refine Fin.cases (motive := fun r : Fin (depth + 2) =>
              (prefixTower r).TerminalSpace.carrier =
                PiLp 2 (fun _ : prefixSite r => SUNLieCoord Nc))
              ?_ (fun j => ?_) r
            · rfl
            · exact Tail'.levelCarrierEq j
          let prefixEquiv : ∀ r : Fin (depth + 2),
              (prefixTower r).TerminalSpace.carrier ≃ₗᵢ[ℝ]
                PiLp 2 (fun _ : prefixSite r => SUNLieCoord Nc) := by
            intro r
            refine Fin.cases (motive := fun r : Fin (depth + 2) =>
              (prefixTower r).TerminalSpace.carrier ≃ₗᵢ[ℝ]
                PiLp 2 (fun _ : prefixSite r => SUNLieCoord Nc))
              ?_ (fun j => ?_) r
            · exact LinearIsometryEquiv.refl ℝ _
            · exact Tail'.levelEquiv j
          refine ⟨CMP99SourceRetainedPhysicalTower.mk
            prefixTower ?_ ?_
            rfl
            prefixNextAverage prefixQprimeSucc
            prefixSite prefixCarrierEq prefixEquiv⟩
          · intro r
            refine Fin.cases ?_ (fun j => ?_) r
            · rfl
            · change (succPrefix j).depth = j.succ.val
              rw [CMP99SourceWeightedRegionalTower.depth_step]
              rw [Tail'.towerAt_depth]
              simp
          · intro r
            refine Fin.cases ?_ (fun j => ?_) r
            · change spacing = (M : ℝ) ^ 0 * spacing
              simp
            · change (succPrefix j).terminalSpacing =
                (M : ℝ) ^ j.succ.val * spacing
              change (Tail'.towerAt j).terminalSpacing =
                (M : ℝ) ^ (j.val + 1) * spacing
              rw [Tail'.towerAt_terminalSpacing]
              rw [pow_succ]
              ring

/-- Canonical retained physical tower selected from the source recursion. -/
noncomputable def cmp99SourceRetainedPhysicalTower
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    CMP99SourceRetainedPhysicalTower rho
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
      M spacing background depth :=
  Classical.choice
    (nonempty_cmp99SourceRetainedPhysicalTower hd hM rho Omega depth spacing
      epsilon background chain fineSmall)

/-- Every retained prefix carries the exact source coisometry normalization;
it is inherited from the literal weighted regional construction. -/
theorem CMP99SourceRetainedPhysicalTower.prefix_comp_weightedAdjoint
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)} {depth : ℕ}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (r : Fin (depth + 1)) :
    (T.towerAt r).Qprime.comp (T.towerAt r).weightedAdjoint =
      ContinuousLinearMap.id ℝ (T.towerAt r).TerminalSpace.carrier :=
  (T.towerAt r).Qprime_comp_weightedAdjoint

/-- Public exact operator-order equation for consecutive physical prefixes. -/
theorem CMP99SourceRetainedPhysicalTower.Qprime_succ
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)} {depth : ℕ}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (k : Fin depth) :
    (T.towerAt k.succ).Qprime =
      (T.nextAverage k).comp (T.towerAt k.castSucc).Qprime :=
  T.towerAt_succ_Qprime k

end

end YangMills.RG
