import YangMills.RG.BalabanCMP99SourceLocalizedWeightedQprimeTower
import YangMills.RG.BalabanCMP99SourceSelectedNextBackgroundLocality
import YangMills.RG.BalabanCMP99SourceGeneratedQprimeRowMass

/-!


# Canonical-extension theorem for the localized Qprime tower

The localized tower is compared with the literal canonical source tower of
any globally admissible extension that agrees with the local background on
the recursively generated retained read carrier.  The proof does not assume
equality of a complete next background or of either Qprime operator.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

private theorem cmp99SourceTerminalCLMTransport_eq_of_heq_local
    {E F G H E' F' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F') (hG : G = E') (hH : H = F')
    (C : E.carrier →L[ℝ] F.carrier)
    (D : G.carrier →L[ℝ] H.carrier) (hCD : HEq C D) :
    cmp99SourceTerminalCLMTransport hE hF C =
      cmp99SourceTerminalCLMTransport hG hH D := by
  subst E'
  subst F'
  subst G
  subst H
  exact eq_of_heq hCD

/-- On a selected positive coarse bond, the localized next background agrees
with the canonical source next background of a globally small extension.
Both sides reduce to the same literal Ubar value; the equality is not an input.
-/
theorem cmp99SourceLocalizedNextBackground_apply_pos_eq_sourceOfFineSmall
    {N' : ℕ} [NeZero N']
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilon <
      cmp99UbarNoWindingThreshold Nc)
    (coarseBonds : Finset (PhysicalBond d N'))
    (localSmallU : ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds
        (Nc := Nc) coarseBonds,
      ‖(U (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (fineSmallV : ∀ e : ConcreteEdge d (M * N'),
      ‖(V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hUV : ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds
        (Nc := Nc) coarseBonds,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q))
    (b : PhysicalBond d N') (hb : b ∈ coarseBonds) :
    let ScaleV : CMP99SourceNormalizedRegionalScale Omega V :=
      CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega V hOmega
        epsilon epsilon_nonneg noWinding fineSmallV
    cmp99SourceLocalizedNextBackground hd hM U epsilon epsilon_nonneg
        noWinding coarseBonds localSmallU (positiveEdgeOfPhysicalBond b) =
      ScaleV.toSourceScale.data.nextBackground
        (positiveEdgeOfPhysicalBond b) := by
  let B_V := cmp99SourceUbarFineNoWindingBudget
    (d := d) (M := M) (Nc := Nc) epsilon noWinding
  have hdevV : ∀ (b : PhysicalBond d N') (x : FinBox d (M * N')),
      x ∈ blockOf M N' b.1 →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          V (cmp99SourceBaseCoarseBackground V)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤ B_V.δ := by
    intro b x hx
    simpa only [B_V, cmp99SourceUbarFineNoWindingBudget_delta] using
      norm_cmp99SourceUbarDeviationLogArg_le_fineRadius
        hd hM V epsilon epsilon_nonneg fineSmallV b x hx
  dsimp only [CMP99SourceNormalizedRegionalScale.ofFineSmall,
    CMP99SourceRegionalScale.ofFineSmall,
    cmp99SourceRegionalScaleDataOfFineSmall,
    cmp99SourceRegionalScaleDataOfDeviationBudget]
  rw [cmp99SourceLocalizedNextBackground_apply_pos_of_mem
    hd hM U epsilon epsilon_nonneg noWinding coarseBonds localSmallU b hb]
  apply Subtype.ext
  change
    (cmp99SourceLocalizedUbarBlock hd hM U epsilon epsilon_nonneg
        noWinding b _ : Matrix (Fin Nc) (Fin Nc) ℂ) =
      (cmp99SourcePhysicalUbarBlockOfDeviationBudget
        (d := d) (M := M) (N' := N') (Nc := Nc) V B_V hdevV b :
          Matrix (Fin Nc) (Fin Nc) ℂ)
  rw [cmp99SourceLocalizedUbarBlock_coe_eq_Ubar,
    cmp99SourcePhysicalUbarBlockOfDeviationBudget_coe_eq_Ubar]
  exact cmp99SourcePhysicalUbar_eq_of_eqOn_selectedReadBonds
    U V coarseBonds hUV b hb

/-- The locally generated tower has the same literal retained Qprime as the
canonical source tower of any globally admissible extension agreeing on the
exact recursive carrier.  Global smallness is required only of the extension,
not of the local background. -/
theorem CMP99SourceActiveRegionChain.localizedWeightedQprimeTower_Qprime_eq_canonicalExtension
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ)
      (U V : PhysicalGaugeBackground d N Nc)
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (localSmallU : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
        ‖(U (positiveEdgeOfPhysicalBond q) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (fineSmallV : ∀ e : ConcreteEdge d N,
        ‖(V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      (∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
        U (positiveEdgeOfPhysicalBond q) =
          V (positiveEdgeOfPhysicalBond q)) →
      let LU := regions.localizedWeightedQprimeTower hd hM rho spacing epsilon U
        chain localSmallU
      let TV := regions.weightedQprimeTower hd hM rho spacing epsilon V chain
        fineSmallV
      let hLU := regions.localizedWeightedQprimeTower_terminalSpace_eq
        hd hM rho spacing epsilon U chain localSmallU
      let hTV := regions.weightedQprimeTower_terminalSpace_eq
        hd hM rho spacing epsilon V chain fineSmallV
      cmp99SourceTerminalCLMTransport
          (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F := LU.TerminalSpace) (F' := regions.terminalHilbertSpace Nc)
          rfl hLU LU.Qprime =
        cmp99SourceTerminalCLMTransport
          (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F := TV.TerminalSpace) (F' := regions.terminalHilbertSpace Nc)
          rfl hTV TV.Qprime := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon U V chain localSmallU fineSmallV hUV
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon U V chain localSmallU fineSmallV hUV
      letI : NeZero (M * N') := inferInstance
      let tailBonds := tail.retainedFineReadBonds (Nc := Nc)
      have tailPullSmallU : ∀ q ∈
          cmp99SourceUbarFineReadBondsOfCoarseBonds (Nc := Nc) tailBonds,
          ‖(U (positiveEdgeOfPhysicalBond q) :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon :=
        boundOn_tailUbarReadBonds_of_boundOn_retainedFineReadBonds
          Omega hOmega tail U epsilon localSmallU
      have tailPullEq : ∀ q ∈
          cmp99SourceUbarFineReadBondsOfCoarseBonds (Nc := Nc) tailBonds,
          U (positiveEdgeOfPhysicalBond q) =
            V (positiveEdgeOfPhysicalBond q) :=
        eqOn_tailUbarReadBonds_of_eqOn_retainedFineReadBonds
          Omega hOmega tail U V hUV
      let nextU : PhysicalGaugeBackground d N' Nc :=
        cmp99SourceLocalizedNextBackground hd hM U epsilon
          chain.epsilon_nonneg chain.head_noWinding tailBonds tailPullSmallU
      let ScaleV : CMP99SourceNormalizedRegionalScale Omega V :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega V hOmega
          epsilon chain.epsilon_nonneg chain.head_noWinding fineSmallV
      have nextSmallU : ∀ e : ConcreteEdge d N',
          ‖(nextU e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        exact norm_cmp99SourceLocalizedNextBackground_sub_one_le
          hd hM U epsilon chain.epsilon_nonneg chain.head_noWinding
          chain.head_logSmall tailBonds tailPullSmallU e
      have nextSmallV : ∀ e : ConcreteEdge d N',
          ‖(ScaleV.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [ScaleV, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega V (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmallV e
      have headEq :
          cmp99SourceTransportedBlockAverageCLM Omega
              (cmp99SourceWeightedPhysicalTransport rho U) =
            cmp99SourceTransportedBlockAverageCLM Omega
              (cmp99SourceWeightedPhysicalTransport rho V) :=
        cmp99SourceTransportedBlockAverageCLM_eq_of_eqOn_retainedFineReadBonds
          rho Omega hOmega tail U V hUV
      have nextEq : ∀ q ∈ tail.retainedFineReadBonds (Nc := Nc),
          nextU (positiveEdgeOfPhysicalBond q) =
            ScaleV.toSourceScale.data.nextBackground
              (positiveEdgeOfPhysicalBond q) := by
        intro q hq
        exact cmp99SourceLocalizedNextBackground_apply_pos_eq_sourceOfFineSmall
          hd hM Omega hOmega U V epsilon chain.epsilon_nonneg
          chain.head_noWinding tailBonds tailPullSmallU fineSmallV tailPullEq
          q hq
      have tailEq := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        nextU ScaleV.toSourceScale.data.nextBackground chain.tail
        (fun q _ => nextSmallU (positiveEdgeOfPhysicalBond q))
        nextSmallV nextEq
      let LocalTail := tail.localizedWeightedQprimeTower hd hM rho
        ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
        nextU chain.tail (fun q _ =>
          nextSmallU (positiveEdgeOfPhysicalBond q))
      let CanonicalTail := tail.weightedQprimeTower hd hM rho
        ((M : ℝ) * spacing) (cmp99SourceUbarNextFineRadius d M epsilon)
        ScaleV.toSourceScale.data.nextBackground chain.tail nextSmallV
      let hLocalTail := tail.localizedWeightedQprimeTower_terminalSpace_eq
        hd hM rho ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon) nextU chain.tail
        (fun q _ => nextSmallU (positiveEdgeOfPhysicalBond q))
      let hCanonicalTail := tail.weightedQprimeTower_terminalSpace_eq
        hd hM rho ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        ScaleV.toSourceScale.data.nextBackground chain.tail nextSmallV
      let OuterLocal :=
        CMP99SourceActiveRegionChain.localizedWeightedQprimeTower
          (CMP99SourceActiveRegionChain.step Omega hOmega tail)
          hd hM rho spacing epsilon U chain localSmallU
      let OuterCanonical :=
        CMP99SourceActiveRegionChain.weightedQprimeTower
          (CMP99SourceActiveRegionChain.step Omega hOmega tail)
          hd hM rho spacing epsilon V chain fineSmallV
      let hOuterLocal :=
        CMP99SourceActiveRegionChain.localizedWeightedQprimeTower_terminalSpace_eq
          (CMP99SourceActiveRegionChain.step Omega hOmega tail)
          hd hM rho spacing epsilon U chain localSmallU
      let hOuterCanonical :=
        CMP99SourceActiveRegionChain.weightedQprimeTower_terminalSpace_eq
          (CMP99SourceActiveRegionChain.step Omega hOmega tail)
          hd hM rho spacing epsilon V chain fineSmallV
      let HeadU := cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho U)
      let HeadV := cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho V)
      let LocalQ := cmp99SourceTerminalCLMTransport
        (E := cmp99SourcePhysicalTerminalHilbertSpace Nc
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
        (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
        (F := LocalTail.TerminalSpace) (F' := tail.terminalHilbertSpace Nc)
        rfl hLocalTail LocalTail.Qprime
      let CanonicalQ := cmp99SourceTerminalCLMTransport
        (E := cmp99SourcePhysicalTerminalHilbertSpace Nc
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
        (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
        (F := CanonicalTail.TerminalSpace) (F' := tail.terminalHilbertSpace Nc)
        rfl hCanonicalTail CanonicalTail.Qprime
      have tailEq' : LocalQ = CanonicalQ := tailEq
      have headEq' : HeadU = HeadV := headEq
      have composedEq : LocalQ.comp HeadU = CanonicalQ.comp HeadV := by
        rw [tailEq']
        exact congrArg
          (fun h : (cmp99SourcePhysicalTerminalHilbertSpace Nc Omega).carrier
              →L[ℝ]
                (cmp99SourcePhysicalTerminalHilbertSpace Nc
                  (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)).carrier =>
            CanonicalQ.comp h) headEq'
      have rawLocal : HEq OuterLocal.Qprime
          (LocalTail.Qprime.comp HeadU) := by
        dsimp only [OuterLocal, LocalTail, HeadU]
        rfl
      have rawCanonical : HEq OuterCanonical.Qprime
          (CanonicalTail.Qprime.comp HeadV) := by
        dsimp only [OuterCanonical, CanonicalTail, HeadV]
        rfl
      have leftBridge :
          cmp99SourceTerminalCLMTransport
              (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (F := OuterLocal.TerminalSpace)
              (F' := tail.terminalHilbertSpace Nc)
              rfl hOuterLocal OuterLocal.Qprime =
            cmp99SourceTerminalCLMTransport
              (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (F := LocalTail.TerminalSpace)
              (F' := tail.terminalHilbertSpace Nc) rfl hLocalTail
              (LocalTail.Qprime.comp HeadU) :=
        cmp99SourceTerminalCLMTransport_eq_of_heq_local
          (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F := OuterLocal.TerminalSpace)
          (G := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (H := LocalTail.TerminalSpace)
          (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F' := tail.terminalHilbertSpace Nc)
          rfl hOuterLocal rfl hLocalTail OuterLocal.Qprime
            (LocalTail.Qprime.comp HeadU) rawLocal
      have rightBridge :
          cmp99SourceTerminalCLMTransport
              (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (F := OuterCanonical.TerminalSpace)
              (F' := tail.terminalHilbertSpace Nc) rfl hOuterCanonical
              OuterCanonical.Qprime =
            cmp99SourceTerminalCLMTransport
              (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (F := CanonicalTail.TerminalSpace)
              (F' := tail.terminalHilbertSpace Nc) rfl hCanonicalTail
              (CanonicalTail.Qprime.comp HeadV) :=
        cmp99SourceTerminalCLMTransport_eq_of_heq_local
          (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F := OuterCanonical.TerminalSpace)
          (G := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (H := CanonicalTail.TerminalSpace)
          (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F' := tail.terminalHilbertSpace Nc)
          rfl hOuterCanonical rfl hCanonicalTail OuterCanonical.Qprime
            (CanonicalTail.Qprime.comp HeadV) rawCanonical
      have leftComp :
          cmp99SourceTerminalCLMTransport
              (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (F := LocalTail.TerminalSpace)
              (F' := tail.terminalHilbertSpace Nc) rfl hLocalTail
              (LocalTail.Qprime.comp HeadU) = LocalQ.comp HeadU := by
        exact (cmp99SourceTerminalCLMTransport_comp
          (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F := cmp99SourcePhysicalTerminalHilbertSpace Nc
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
          (G := LocalTail.TerminalSpace)
          (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F' := cmp99SourcePhysicalTerminalHilbertSpace Nc
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
          (G' := tail.terminalHilbertSpace Nc)
          rfl rfl hLocalTail LocalTail.Qprime HeadU).symm
      have rightComp :
          cmp99SourceTerminalCLMTransport
              (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
              (F := CanonicalTail.TerminalSpace)
              (F' := tail.terminalHilbertSpace Nc) rfl hCanonicalTail
              (CanonicalTail.Qprime.comp HeadV) = CanonicalQ.comp HeadV := by
        exact (cmp99SourceTerminalCLMTransport_comp
          (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F := cmp99SourcePhysicalTerminalHilbertSpace Nc
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
          (G := CanonicalTail.TerminalSpace)
          (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F' := cmp99SourcePhysicalTerminalHilbertSpace Nc
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
          (G' := tail.terminalHilbertSpace Nc)
          rfl rfl hCanonicalTail CanonicalTail.Qprime HeadV).symm
      exact leftBridge.trans (leftComp.trans
        (composedEq.trans (rightComp.symm.trans rightBridge.symm)))

end

end YangMills.RG
