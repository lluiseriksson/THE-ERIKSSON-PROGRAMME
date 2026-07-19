/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRecursivePhysicalTower
import YangMills.RG.BalabanCMP99CoarseDerivativeRegional

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

namespace CMP99SourceUbarRadiusChain

/-- The initial radius of every source chain is nonnegative. -/
theorem epsilon_nonneg {depth : ℕ} {epsilon : ℝ}
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) :
    0 ≤ epsilon := by
  cases chain with
  | stop _ h => exact h
  | step _ h _ _ _ => exact h

/-- The head of a positive-depth chain supplies the physical no-winding
certificate without exposing the proof-valued constructor to data recursion. -/
theorem head_noWinding {depth : ℕ} {epsilon : ℝ}
    (chain : CMP99SourceUbarRadiusChain d M Nc (depth + 1) epsilon) :
    cmp99SourceUbarFineDeviationRadius d M epsilon <
      cmp99UbarNoWindingThreshold Nc := by
  cases chain with
  | step _ _ h _ _ => exact h

/-- The head logarithmic smallness certificate of a positive-depth chain. -/
theorem head_logSmall {depth : ℕ} {epsilon : ℝ}
    (chain : CMP99SourceUbarRadiusChain d M Nc (depth + 1) epsilon) :
    cmp99UbarLogRadius
        (cmp99SourceUbarFineNoWindingBudget epsilon chain.head_noWinding) < 1 := by
  cases chain with
  | step _ _ _ h _ => exact h

/-- Proof-valued tail of a positive-depth chain. -/
theorem tail {depth : ℕ} {epsilon : ℝ}
    (chain : CMP99SourceUbarRadiusChain d M Nc (depth + 1) epsilon) :
    CMP99SourceUbarRadiusChain d M Nc depth
      (cmp99SourceUbarNextFineRadius d M epsilon) := by
  cases chain with
  | step _ _ _ _ h => exact h

end CMP99SourceUbarRadiusChain

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
  /-- Every literal retained one-step average has the exact source
  counting-space contraction factor `M⁻ᵈ`. -/
  nextAverage_norm_sq_le : ∀ k : Fin depth,
    ∀ phi : (towerAt k.castSucc).TerminalSpace.carrier,
      ‖nextAverage k phi‖ ^ 2 ≤
        cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2
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

/-- Direct recursive construction of every retained prefix from the literal
`Ubar` chain.  This definition does not select an arbitrary inhabitant from a
nonemptiness proof: its successor branch uses exactly the physical first-scale
average and then recurses on the generated coarse background. -/
noncomputable def cmp99SourceGeneratedRetainedPhysicalTower
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) :
    ∀ (depth : ℕ) (spacing epsilon : ℝ)
      (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc)),
      CMP99SourceUbarRadiusChain d M Nc depth epsilon →
      (∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
      CMP99SourceRetainedPhysicalTower rho
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
        M spacing background depth := by
  intro depth
  induction depth with
  | zero =>
      intro spacing epsilon background _chain _fineSmall
      refine CMP99SourceRetainedPhysicalTower.mk
        (fun _ => CMP99SourceWeightedRegionalTower.stop
          (g := SUNLieCoord Nc) Omega spacing) ?_ ?_
        rfl
        (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)
        (fun k => Fin.elim0 k)
        (fun _ => ActiveGaugeRegion.Site Omega)
        (fun _ => rfl)
        (fun _ => LinearIsometryEquiv.refl ℝ _)
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
      let epsilon_nonneg := chain.epsilon_nonneg
      let noWinding := chain.head_noWinding
      let logSmall := chain.head_logSmall
      let tailChain := chain.tail
      exact (by
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
          let Tail := ih ((M : ℝ) * spacing)
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
          let prefixNextAverageNorm : ∀ k : Fin (depth + 1),
              ∀ phi : (prefixTower k.castSucc).TerminalSpace.carrier,
                ‖prefixNextAverage k phi‖ ^ 2 ≤
                  cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2 := by
            intro k
            refine Fin.cases (motive := fun k : Fin (depth + 1) =>
              ∀ phi : (prefixTower k.castSucc).TerminalSpace.carrier,
                ‖prefixNextAverage k phi‖ ^ 2 ≤
                  cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2)
              ?_ (fun s => ?_) k
            · intro phi
              simp only [prefixNextAverage, prefixTower, Fin.cases_zero]
              have hQnorm : ∀ eta : ActiveGaugeZeroCochain
                    (cmp99ActiveCoarseRegion
                      (M := M) (N' := cmp99RegionalLatticeSize M N depth)
                      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
                    (SUNLieCoord Nc),
                  ‖(Tail'.towerAt 0).Qprime eta‖ = ‖eta‖ := by
                rw [Tail'.towerAt_zero]
                intro eta
                rfl
              change
                ‖(Tail'.towerAt 0).Qprime
                  (cmp99SourceTransportedBlockAverageCLM
                    (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
                    (cmp99SourceWeightedPhysicalTransport rho background) phi)‖ ^ 2 ≤
                  cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2
              rw [hQnorm]
              exact norm_cmp99SourceRegionalAverage_sq_le
                (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
                (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
                rho background phi
            · intro phi
              exact Tail'.nextAverage_norm_sq_le s phi
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
          refine CMP99SourceRetainedPhysicalTower.mk
            prefixTower ?_ ?_
            rfl
            prefixNextAverage prefixQprimeSucc prefixNextAverageNorm
            prefixSite prefixCarrierEq prefixEquiv
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
              ring)

/-- The direct physical construction witnesses nonemptiness.  This theorem is
retained for callers that only need existence. -/
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
  intro depth spacing epsilon background chain fineSmall
  exact ⟨cmp99SourceGeneratedRetainedPhysicalTower hd hM rho Omega depth
    spacing epsilon background chain fineSmall⟩

/-- Canonical retained physical tower, definitionally generated by the source
recursion rather than selected from an existence theorem. -/
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
  cmp99SourceGeneratedRetainedPhysicalTower hd hM rho Omega depth spacing
    epsilon background chain fineSmall

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

/-- Public source contraction for every consecutive retained physical
prefix.  It is generated by the private recursive constructor. -/
theorem CMP99SourceRetainedPhysicalTower.norm_nextAverage_sq_le
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)} {depth : ℕ}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (k : Fin depth)
    (phi : (T.towerAt k.castSucc).TerminalSpace.carrier) :
    ‖T.nextAverage k phi‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2 :=
  T.nextAverage_norm_sq_le k phi

/-- Every consecutive retained physical prefix contracts the original fine
field by the exact source counting-space factor `M⁻ᵈ`.  The theorem exposes
the printed recursive operator `Q'_(k+1) = Q_k(U_k) Q'_k`, rather than an
unrelated family of scalar estimates. -/
theorem CMP99SourceRetainedPhysicalTower.norm_Qprime_succ_sq_le
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)} {depth : ℕ}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (k : Fin depth) (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖(T.towerAt k.succ).Qprime phi‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d *
        ‖(T.towerAt k.castSucc).Qprime phi‖ ^ 2 := by
  rw [T.Qprime_succ, ContinuousLinearMap.comp_apply]
  exact T.norm_nextAverage_sq_le k ((T.towerAt k.castSucc).Qprime phi)

/-- Iterating the literal source averages gives the exact volume factor at
every retained prefix.  In dimension `d`, the `r`-th prefix therefore costs
`(M⁻ᵈ)^r`, with no independently supplied multiscale norm certificate. -/
theorem CMP99SourceRetainedPhysicalTower.norm_Qprime_sq_le_pow
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)} {depth : ℕ}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (r : Fin (depth + 1)) (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖(T.towerAt r).Qprime phi‖ ^ 2 ≤
      (cmp99SourceBlockAverageWeight M d) ^ r.val * ‖phi‖ ^ 2 := by
  refine Fin.induction ?_ ?_ r
  · rw [T.towerAt_zero]
    dsimp [CMP99SourceWeightedRegionalTower.stop]
    change ‖phi‖ ^ 2 ≤
      (cmp99SourceBlockAverageWeight M d) ^ 0 * ‖phi‖ ^ 2
    simp
  · intro k ih
    have hw : 0 ≤ cmp99SourceBlockAverageWeight M d := by
      unfold cmp99SourceBlockAverageWeight
      positivity
    calc
      ‖(T.towerAt k.succ).Qprime phi‖ ^ 2 ≤
          cmp99SourceBlockAverageWeight M d *
            ‖(T.towerAt k.castSucc).Qprime phi‖ ^ 2 :=
        T.norm_Qprime_succ_sq_le k phi
      _ ≤ cmp99SourceBlockAverageWeight M d *
            ((cmp99SourceBlockAverageWeight M d) ^ k.val * ‖phi‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ih hw
      _ = (cmp99SourceBlockAverageWeight M d) ^ k.succ.val * ‖phi‖ ^ 2 := by
        simp only [Fin.val_succ, pow_succ]
        ring

end

end YangMills.RG
