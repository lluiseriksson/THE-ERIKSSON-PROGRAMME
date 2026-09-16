import YangMills.RG.BalabanCMP99SourceLocalizedTowerCanonicalExtension

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

variable {d M Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero Nc]

private theorem cmp99SourceTerminalCLMTransport_right_injective
    {E F F' : CMP99SourceWeightedTowerHilbertSpace} (hF : F = F') :
    Function.Injective
      (cmp99SourceTerminalCLMTransport
        (E := E) (E' := E) (F := F) (F' := F') rfl hF) := by
  subst F'
  intro C D h
  exact h

/-- Exterior changes away from the recursively generated exact read carrier
do not change the literal retained physical `Qprime`.  The equality is stated
after canonical terminal-bundle transport, so it compares the source towers
without identifying proof-dependent terminal bundles by definition. -/
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
      let TU := regions.weightedQprimeTower hd hM rho spacing epsilon U chain
        fineSmallU
      let TV := regions.weightedQprimeTower hd hM rho spacing epsilon V chain
        fineSmallV
      let hTU := regions.weightedQprimeTower_terminalSpace_eq hd hM rho
        spacing epsilon U chain fineSmallU
      let hTV := regions.weightedQprimeTower_terminalSpace_eq hd hM rho
        spacing epsilon V chain fineSmallV
      cmp99SourceTerminalCLMTransport
          (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F := TU.TerminalSpace) (F' := regions.terminalHilbertSpace Nc)
          rfl hTU TU.Qprime =
        cmp99SourceTerminalCLMTransport
          (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
          (F := TV.TerminalSpace) (F' := regions.terminalHilbertSpace Nc)
          rfl hTV TV.Qprime := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon U V chain fineSmallU fineSmallV hUV
  have localSmallU : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(U (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon := by
    intro q _
    exact fineSmallU (positiveEdgeOfPhysicalBond q)
  have hUU :=
    regions.localizedWeightedQprimeTower_Qprime_eq_canonicalExtension
      hd hM rho spacing epsilon U U chain localSmallU fineSmallU
      (by intro q hq; rfl)
  have hUV' :=
    regions.localizedWeightedQprimeTower_Qprime_eq_canonicalExtension
      hd hM rho spacing epsilon U V chain localSmallU fineSmallV hUV
  exact hUU.symm.trans hUV'

end

end YangMills.RG
