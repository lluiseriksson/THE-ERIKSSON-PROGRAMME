import YangMills.RG.BalabanCMP99SourceLocalizedWeightedQprimeTower
import YangMills.RG.BalabanCMP99SourceRetainedQprimeLocality

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

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
  dsimp only
  rw [cmp99SourceLocalizedNextBackground_apply_pos_of_mem
    hd hM U epsilon epsilon_nonneg noWinding coarseBonds localSmallU b hb]
  apply Subtype.ext
  change
    (cmp99SourceLocalizedUbarBlock hd hM U epsilon epsilon_nonneg
        noWinding b _ : Matrix (Fin Nc) (Fin Nc) ℂ) =
      (cmp99PhysicalUbarBlockOfDeviationBudget V
        (cmp99SourceBaseCoarseBackground V)
        (cmp99SourceUbarGamma1 (G := SUN Nc))
        (cmp99SourceUbarGamma2 (G := SUN Nc))
        (cmp99SourceUbarGamma3 (G := SUN Nc)) _ _ b :
          Matrix (Fin Nc) (Fin Nc) ℂ)
  rw [cmp99SourceLocalizedUbarBlock_coe_eq_Ubar,
    cmp99PhysicalUbarBlockOfDeviationBudget_coe_eq_Ubar]
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
      (regions.localizedWeightedQprimeTower hd hM rho spacing epsilon U
          chain localSmallU).Qprime =
        (regions.weightedQprimeTower hd hM rho spacing epsilon V chain
          fineSmallV).Qprime := by
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
      change
        (tail.localizedWeightedQprimeTower hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon) nextU chain.tail
            (fun q _ => nextSmallU (positiveEdgeOfPhysicalBond q))).Qprime.comp
          (cmp99SourceTransportedBlockAverageCLM Omega
            (cmp99SourceWeightedPhysicalTransport rho U)) =
        (tail.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            ScaleV.toSourceScale.data.nextBackground chain.tail
            nextSmallV).Qprime.comp
          (cmp99SourceTransportedBlockAverageCLM Omega
            (cmp99SourceWeightedPhysicalTransport rho V))
      rw [tailEq, headEq]

end

end YangMills.RG
