import YangMills.RG.BalabanCMP99SourceRetainedFineExtension

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# Retain every prefix of the localized source tower

One private recursion constructs the localized prefixes together with the
canonical prefixes of the internally generated retained identity extension.
The equality of every Qprime prefix is derived from the exact head-average
and selected next-background locality theorems.  No family of towers or
operator equalities is supplied by the caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Auxiliary pair for two backgrounds agreeing on the recursive carrier.
The constructor remains private and is used only to build the source-facing
retained object below. -/
private structure CMP99SourceLocalizedCanonicalRetainedAux
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (localBackground canonicalBackground : PhysicalGaugeBackground d N Nc)
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (localSmall : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(localBackground (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (canonicalSmall : ∀ e : ConcreteEdge d N,
      ‖(canonicalBackground e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (agree : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      localBackground (positiveEdgeOfPhysicalBond q) =
        canonicalBackground (positiveEdgeOfPhysicalBond q)) where
  private mk ::
  localTowerAt : Fin (depth + 1) →
    CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega spacing
  canonicalTowerAt : Fin (depth + 1) →
    CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega spacing
  localTowerAt_depth : ∀ r, (localTowerAt r).depth = r.val
  canonicalTowerAt_depth : ∀ r, (canonicalTowerAt r).depth = r.val
  localTowerAt_zero : localTowerAt 0 =
    CMP99SourceWeightedRegionalTower.stop
      (g := SUNLieCoord Nc) Omega spacing
  canonicalTowerAt_zero : canonicalTowerAt 0 =
    CMP99SourceWeightedRegionalTower.stop
      (g := SUNLieCoord Nc) Omega spacing
  prefixQprime_eq : ∀ r,
    (localTowerAt r).Qprime = (canonicalTowerAt r).Qprime
  localTerminal_eq_generated :
    localTowerAt (Fin.last depth) =
      regions.localizedWeightedQprimeTower hd hM rho spacing epsilon
        localBackground chain localSmall
  canonicalTerminal_eq_generated :
    canonicalTowerAt (Fin.last depth) =
      regions.weightedQprimeTower hd hM rho spacing epsilon
        canonicalBackground chain canonicalSmall

/-- Private recursion generating both retained prefix families and their
pointwise Qprime equality. -/
private noncomputable def cmp99SourceLocalizedCanonicalRetainedAux
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ)
      (localBackground canonicalBackground : PhysicalGaugeBackground d N Nc)
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (localSmall : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
        ‖(localBackground (positiveEdgeOfPhysicalBond q) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (canonicalSmall : ∀ e : ConcreteEdge d N,
        ‖(canonicalBackground e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (agree : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
        localBackground (positiveEdgeOfPhysicalBond q) =
          canonicalBackground (positiveEdgeOfPhysicalBond q)),
      CMP99SourceLocalizedCanonicalRetainedAux regions hd hM rho spacing
        epsilon localBackground canonicalBackground chain localSmall
        canonicalSmall agree := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon localBackground canonicalBackground chain
        localSmall canonicalSmall agree
      let stopTower := CMP99SourceWeightedRegionalTower.stop
        (g := SUNLieCoord Nc) Omega spacing
      refine CMP99SourceLocalizedCanonicalRetainedAux.mk
        (fun _ => stopTower) (fun _ => stopTower) ?_ ?_ rfl rfl ?_ rfl rfl
      · intro r
        have hr : r = 0 := Fin.eq_zero r
        subst r
        rfl
      · intro r
        have hr : r = 0 := Fin.eq_zero r
        subst r
        rfl
      · intro r
        have hr : r = 0 := Fin.eq_zero r
        subst r
        rfl
  | @step N' tailDepth _ Omega hOmega tail ih =>
      intro spacing epsilon localBackground canonicalBackground chain
        localSmall canonicalSmall agree
      letI : NeZero (M * N') := inferInstance
      let tailBonds := tail.retainedFineReadBonds (Nc := Nc)
      have tailPullSmall : ∀ q ∈
          cmp99SourceUbarFineReadBondsOfCoarseBonds (Nc := Nc) tailBonds,
          ‖(localBackground (positiveEdgeOfPhysicalBond q) :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon :=
        boundOn_tailUbarReadBonds_of_boundOn_retainedFineReadBonds
          Omega hOmega tail localBackground epsilon localSmall
      have tailPullEq : ∀ q ∈
          cmp99SourceUbarFineReadBondsOfCoarseBonds (Nc := Nc) tailBonds,
          localBackground (positiveEdgeOfPhysicalBond q) =
            canonicalBackground (positiveEdgeOfPhysicalBond q) :=
        eqOn_tailUbarReadBonds_of_eqOn_retainedFineReadBonds
          Omega hOmega tail localBackground canonicalBackground agree
      let nextLocal : PhysicalGaugeBackground d N' Nc :=
        cmp99SourceLocalizedNextBackground hd hM localBackground epsilon
          chain.epsilon_nonneg chain.head_noWinding tailBonds tailPullSmall
      let CanonicalScale : CMP99SourceNormalizedRegionalScale
          Omega canonicalBackground :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega
          canonicalBackground hOmega epsilon chain.epsilon_nonneg
          chain.head_noWinding canonicalSmall
      have nextLocalSmall : ∀ e : ConcreteEdge d N',
          ‖(nextLocal e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        exact norm_cmp99SourceLocalizedNextBackground_sub_one_le
          hd hM localBackground epsilon chain.epsilon_nonneg
          chain.head_noWinding chain.head_logSmall tailBonds tailPullSmall e
      have nextCanonicalSmall : ∀ e : ConcreteEdge d N',
          ‖(CanonicalScale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [CanonicalScale,
          CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega canonicalBackground
            (cmp99SourceBlockAverageWeight M d) epsilon
            chain.epsilon_nonneg chain.head_noWinding chain.head_logSmall
            canonicalSmall e
      have nextAgree : ∀ q ∈ tail.retainedFineReadBonds (Nc := Nc),
          nextLocal (positiveEdgeOfPhysicalBond q) =
            CanonicalScale.toSourceScale.data.nextBackground
              (positiveEdgeOfPhysicalBond q) := by
        intro q hq
        exact cmp99SourceLocalizedNextBackground_apply_pos_eq_sourceOfFineSmall
          hd hM Omega hOmega localBackground canonicalBackground epsilon
          chain.epsilon_nonneg chain.head_noWinding tailBonds tailPullSmall
          canonicalSmall tailPullEq q hq
      let Tail := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        nextLocal CanonicalScale.toSourceScale.data.nextBackground chain.tail
        (fun q _ => nextLocalSmall (positiveEdgeOfPhysicalBond q))
        nextCanonicalSmall nextAgree
      let localHead := CMP99SourceWeightedRegionalTower.stop
        (g := SUNLieCoord Nc) Omega spacing
      let canonicalHead := CMP99SourceWeightedRegionalTower.stop
        (g := SUNLieCoord Nc) Omega spacing
      let localSucc (r : Fin (tailDepth + 1)) :=
        CMP99SourceWeightedRegionalTower.step
          (g := SUNLieCoord Nc) Omega hOmega spacing
          (cmp99SourceWeightedPhysicalTransport rho localBackground)
          (Tail.localTowerAt r)
      let canonicalSucc (r : Fin (tailDepth + 1)) :=
        CMP99SourceWeightedRegionalTower.step
          (g := SUNLieCoord Nc) Omega hOmega spacing
          (cmp99SourceWeightedPhysicalTransport rho canonicalBackground)
          (Tail.canonicalTowerAt r)
      let localTower : Fin (tailDepth + 2) →
          CMP99SourceWeightedRegionalTower
            (g := SUNLieCoord Nc) Omega spacing :=
        Fin.cases localHead localSucc
      let canonicalTower : Fin (tailDepth + 2) →
          CMP99SourceWeightedRegionalTower
            (g := SUNLieCoord Nc) Omega spacing :=
        Fin.cases canonicalHead canonicalSucc
      have headEq :
          cmp99SourceTransportedBlockAverageCLM Omega
              (cmp99SourceWeightedPhysicalTransport rho localBackground) =
            cmp99SourceTransportedBlockAverageCLM Omega
              (cmp99SourceWeightedPhysicalTransport rho canonicalBackground) :=
        cmp99SourceTransportedBlockAverageCLM_eq_of_eqOn_retainedFineReadBonds
          rho Omega hOmega tail localBackground canonicalBackground agree
      have prefixEq : ∀ r : Fin (tailDepth + 2),
          (localTower r).Qprime = (canonicalTower r).Qprime := by
        intro r
        refine Fin.cases ?_ (fun s => ?_) r
        · rfl
        · change (Tail.localTowerAt s).Qprime.comp
              (cmp99SourceTransportedBlockAverageCLM Omega
                (cmp99SourceWeightedPhysicalTransport rho localBackground)) =
            (Tail.canonicalTowerAt s).Qprime.comp
              (cmp99SourceTransportedBlockAverageCLM Omega
                (cmp99SourceWeightedPhysicalTransport rho canonicalBackground))
          rw [Tail.prefixQprime_eq s, headEq]
      refine CMP99SourceLocalizedCanonicalRetainedAux.mk
        localTower canonicalTower ?_ ?_ rfl rfl prefixEq ?_ ?_
      · intro r
        refine Fin.cases ?_ (fun s => ?_) r
        · rfl
        · change (localSucc s).depth = s.succ.val
          rw [CMP99SourceWeightedRegionalTower.depth_step,
            Tail.localTowerAt_depth]
          rfl
      · intro r
        refine Fin.cases ?_ (fun s => ?_) r
        · rfl
        · change (canonicalSucc s).depth = s.succ.val
          rw [CMP99SourceWeightedRegionalTower.depth_step,
            Tail.canonicalTowerAt_depth]
          rfl
      · have hlast : Fin.last (tailDepth + 1) =
            (Fin.last tailDepth).succ := by
          apply Fin.ext
          simp
        rw [hlast]
        change localSucc (Fin.last tailDepth) =
          CMP99SourceWeightedRegionalTower.step
            (g := SUNLieCoord Nc) Omega hOmega spacing
            (cmp99SourceWeightedPhysicalTransport rho localBackground)
            (tail.localizedWeightedQprimeTower hd hM rho
              ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon) nextLocal chain.tail
              (fun q _ => nextLocalSmall (positiveEdgeOfPhysicalBond q)))
        exact congrArg
          (CMP99SourceWeightedRegionalTower.step
            (g := SUNLieCoord Nc) Omega hOmega spacing
            (cmp99SourceWeightedPhysicalTransport rho localBackground))
          Tail.localTerminal_eq_generated
      · have hlast : Fin.last (tailDepth + 1) =
            (Fin.last tailDepth).succ := by
          apply Fin.ext
          simp
        rw [hlast]
        change canonicalSucc (Fin.last tailDepth) =
          CMP99SourceWeightedRegionalTower.step
            (g := SUNLieCoord Nc) Omega hOmega spacing
            (cmp99SourceWeightedPhysicalTransport rho canonicalBackground)
            (tail.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              CanonicalScale.toSourceScale.data.nextBackground chain.tail
              nextCanonicalSmall)
        exact congrArg
          (CMP99SourceWeightedRegionalTower.step
            (g := SUNLieCoord Nc) Omega hOmega spacing
            (cmp99SourceWeightedPhysicalTransport rho canonicalBackground))
          Tail.canonicalTerminal_eq_generated

/-- Source-facing retained prefix package.  Its canonical side is fixed to
the internally generated retained identity extension, so no extension or
prefix family is an input. -/
structure CMP99SourceLocalizedRetainedTower
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : PhysicalGaugeBackground d N Nc)
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (localSmall : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) where
  private mk ::
  localizedTowerAt : Fin (depth + 1) →
    CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega spacing
  canonicalTowerAt : Fin (depth + 1) →
    CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega spacing
  localizedTowerAt_depth : ∀ r, (localizedTowerAt r).depth = r.val
  canonicalTowerAt_depth : ∀ r, (canonicalTowerAt r).depth = r.val
  localizedTowerAt_zero : localizedTowerAt 0 =
    CMP99SourceWeightedRegionalTower.stop
      (g := SUNLieCoord Nc) Omega spacing
  canonicalTowerAt_zero : canonicalTowerAt 0 =
    CMP99SourceWeightedRegionalTower.stop
      (g := SUNLieCoord Nc) Omega spacing
  prefixQprime_eq : ∀ r,
    (localizedTowerAt r).Qprime = (canonicalTowerAt r).Qprime
  localizedTerminal_eq_generated :
    localizedTowerAt (Fin.last depth) =
      regions.localizedWeightedQprimeTower hd hM rho spacing epsilon
        background chain localSmall
  canonicalTerminal_eq_generated :
    canonicalTowerAt (Fin.last depth) =
      regions.weightedQprimeTower hd hM rho spacing epsilon
        (regions.retainedFineExtension background) chain
        (regions.norm_retainedFineExtension_sub_one_le background epsilon
          chain.epsilon_nonneg localSmall)

/-- Construct every localized/canonical prefix by one private recursion. -/
noncomputable def cmp99SourceLocalizedRetainedTower
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ)
      (background : PhysicalGaugeBackground d N Nc)
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (localSmall : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
        ‖(background (positiveEdgeOfPhysicalBond q) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      CMP99SourceLocalizedRetainedTower regions hd hM rho spacing epsilon
        background chain localSmall := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain localSmall
  let extension := regions.retainedFineExtension background
  let extensionSmall := regions.norm_retainedFineExtension_sub_one_le
    background epsilon chain.epsilon_nonneg localSmall
  let agree : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      background (positiveEdgeOfPhysicalBond q) =
        extension (positiveEdgeOfPhysicalBond q) := by
    intro q hq
    exact (regions.retainedFineExtension_apply_pos_of_mem
      background q hq).symm
  let Aux := cmp99SourceLocalizedCanonicalRetainedAux regions hd hM rho
    spacing epsilon background extension chain localSmall extensionSmall agree
  exact CMP99SourceLocalizedRetainedTower.mk
    Aux.localTowerAt Aux.canonicalTowerAt Aux.localTowerAt_depth
    Aux.canonicalTowerAt_depth Aux.localTowerAt_zero
    Aux.canonicalTowerAt_zero Aux.prefixQprime_eq
    Aux.localTerminal_eq_generated Aux.canonicalTerminal_eq_generated

/-- Terminal projection of the internally derived equality of every retained
prefix. -/
theorem CMP99SourceLocalizedRetainedTower.terminalQprime_eq
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    {regions : CMP99SourceActiveRegionChain d M N Omega depth}
    {hd : 2 ≤ d} {hM : 2 ≤ M} {rho : SUNAdjointModel Nc}
    {spacing epsilon : ℝ}
    {background : PhysicalGaugeBackground d N Nc}
    {chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon}
    {localSmall : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon}
    (T : CMP99SourceLocalizedRetainedTower regions hd hM rho spacing epsilon
      background chain localSmall) :
    (T.localizedTowerAt (Fin.last depth)).Qprime =
      (T.canonicalTowerAt (Fin.last depth)).Qprime :=
  T.prefixQprime_eq (Fin.last depth)

end

end YangMills.RG
