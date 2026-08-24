import YangMills.RG.BalabanCMP99SourceSelectedNextBackgroundLocality
import YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# Locality of the literal retained Qprime

The proof recurses on the typed active-region chain.  At every successor the
recursive carrier supplies equality of the literal head average and equality
of the selected positive coordinates of the two internally generated next
backgrounds.  The latter is exactly the induction hypothesis required by the
tail carrier.  No equality of a complete background or supplied operator
equality appears in the interface.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Exterior changes away from the recursively generated exact read carrier
do not change the literal retained physical `Qprime`.  Both towers and every
next background are constructed internally by the source recursion. -/
theorem CMP99SourceActiveRegionChain.weightedQprimeTower_Qprime_eq_of_eqOn_retainedFineReadBonds
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ)
      (U V : PhysicalGaugeBackground d N Nc)
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmallU : ∀ e : ConcreteEdge d N,
        ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (fineSmallV : ∀ e : ConcreteEdge d N,
        ‖(V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      (∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
        U (positiveEdgeOfPhysicalBond q) =
          V (positiveEdgeOfPhysicalBond q)) →
      (regions.weightedQprimeTower hd hM rho spacing epsilon U chain
          fineSmallU).Qprime =
        (regions.weightedQprimeTower hd hM rho spacing epsilon V chain
          fineSmallV).Qprime := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon U V chain fineSmallU fineSmallV hUV
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon U V chain fineSmallU fineSmallV hUV
      letI : NeZero (M * N') := inferInstance
      let ScaleU : CMP99SourceNormalizedRegionalScale Omega U :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega U hOmega
          epsilon chain.epsilon_nonneg chain.head_noWinding fineSmallU
      let ScaleV : CMP99SourceNormalizedRegionalScale Omega V :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega V hOmega
          epsilon chain.epsilon_nonneg chain.head_noWinding fineSmallV
      have nextSmallU : ∀ e : ConcreteEdge d N',
          ‖(ScaleU.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [ScaleU, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega U (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmallU e
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
          ScaleU.toSourceScale.data.nextBackground
              (positiveEdgeOfPhysicalBond q) =
            ScaleV.toSourceScale.data.nextBackground
              (positiveEdgeOfPhysicalBond q) := by
        intro q hq
        apply cmp99SourceNormalizedRegionalScaleOfFineSmall_nextBackground_apply_pos_eq
          hd hM Omega hOmega U V epsilon chain.epsilon_nonneg
            chain.head_noWinding fineSmallU fineSmallV
            (tail.retainedFineReadBonds (Nc := Nc))
        · exact eqOn_tailUbarReadBonds_of_eqOn_retainedFineReadBonds
            Omega hOmega tail U V hUV
        · exact q
        · exact hq
      have tailEq := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        ScaleU.toSourceScale.data.nextBackground
        ScaleV.toSourceScale.data.nextBackground chain.tail
        nextSmallU nextSmallV nextEq
      change
        (tail.weightedQprimeTower hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            ScaleU.toSourceScale.data.nextBackground chain.tail
            nextSmallU).Qprime.comp
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
