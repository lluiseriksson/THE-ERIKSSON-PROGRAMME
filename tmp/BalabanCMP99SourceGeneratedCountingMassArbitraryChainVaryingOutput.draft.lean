import YangMills.RG.BalabanCMP99SourceGeneratedCountingMassVaryingOutput
import YangMills.RG.BalabanCMP99SourceActiveRegionTerminalBlockDiameter

/-!
SCRATCH ONLY: no compiler or axiom-oracle verdict is claimed.

The cold-sealed varying-value theorem is specialized to the canonical
iterated-lift chain.  C6d carries an arbitrary typed source-region chain.
This scratch generalizes only the terminal-fibre counting argument; it does
not accept a cardinality bound or a generated-mass estimate as caller data.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero Nc]

open scoped Classical in
/-- Every terminal-owner fibre of an arbitrary typed source-region chain has
at most the literal block volume `(M^depth)^d`. -/
theorem CMP99SourceActiveRegionChain.card_sameTerminalBlock_le
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (target : ActiveGaugeRegion.Site Omega) :
    (Finset.univ.filter fun source =>
      regions.SameTerminalBlock source target).card ≤ (M ^ depth) ^ d := by
  classical
  let residue : ActiveGaugeRegion.Site Omega → FinBox d (M ^ depth) :=
    fun source i => ⟨(source.1 i).val % M ^ depth,
      Nat.mod_lt _ (pow_pos (NeZero.pos M) depth)⟩
  calc
    (Finset.univ.filter fun source =>
        regions.SameTerminalBlock source target).card ≤
        (Finset.univ : Finset (FinBox d (M ^ depth))).card := by
      apply Finset.card_le_card_of_injOn residue
      · intro source _hsource
        exact Finset.mem_univ _
      · intro source hsource source' hsource' heq
        apply Subtype.ext
        funext i
        apply Fin.ext
        have hs : (source.1 i).val / M ^ depth =
            (target.1 i).val / M ^ depth :=
          regions.div_pow_eq_of_sameTerminalBlock source target
            (Finset.mem_filter.mp hsource).2 i
        have hs' : (source'.1 i).val / M ^ depth =
            (target.1 i).val / M ^ depth :=
          regions.div_pow_eq_of_sameTerminalBlock source' target
            (Finset.mem_filter.mp hsource').2 i
        have hquot : (source.1 i).val / M ^ depth =
            (source'.1 i).val / M ^ depth := hs.trans hs'.symm
        have hrem : (source.1 i).val % M ^ depth =
            (source'.1 i).val % M ^ depth :=
          congrArg Fin.val (congrFun heq i)
        have hxdiv : (source.1 i).val =
            M ^ depth * ((source.1 i).val / M ^ depth) +
              (source.1 i).val % M ^ depth :=
          (Nat.div_add_mod _ _).symm
        have hydiv : (source'.1 i).val =
            M ^ depth * ((source'.1 i).val / M ^ depth) +
              (source'.1 i).val % M ^ depth :=
          (Nat.div_add_mod _ _).symm
        rw [hquot, hrem] at hxdiv
        omega
    _ = (M ^ depth) ^ d := by simp

/-- Source-dependent fixed-output counting-mass bound for an arbitrary typed
source-region chain.  Values are controlled only on the actual terminal
fibre; the block count cancels one normalized averaging weight internally. -/
theorem CMP99SourceActiveRegionChain.sum_norm_generatedCountingMass_varying_le
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (target : ActiveGaugeRegion.Site Omega)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (C : ℝ) (hC : 0 ≤ C)
    (hphi : ∀ source,
      regions.SameTerminalBlock source target → ‖phi source‖ ≤ C) :
    (∑ source,
        ‖regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp source (phi source)) target‖) ≤
      (cmp99SourceBlockAverageWeight M d) ^ depth * C := by
  classical
  letI : NeZero N := regions.neZero
  let fibre := Finset.univ.filter fun source =>
    regions.SameTerminalBlock source target
  have hw : 0 ≤ cmp99SourceBlockAverageWeight M d :=
    cmp99SourceBlockAverageWeight_nonneg M d
  have hterm_nonneg : 0 ≤
      (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) * C :=
    mul_nonneg (pow_nonneg hw _) hC
  calc
    (∑ source,
        ‖regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp source (phi source)) target‖) =
      (∑ source ∈ fibre,
        ‖regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp source (phi source)) target‖) := by
        change (∑ source,
            ‖regions.generatedCountingMass hd hM rho spacing epsilon background
              chain fineSmall (singleFinitePiLp source (phi source)) target‖) =
          (∑ source ∈ Finset.univ.filter (fun source =>
            regions.SameTerminalBlock source target),
            ‖regions.generatedCountingMass hd hM rho spacing epsilon background
              chain fineSmall (singleFinitePiLp source (phi source)) target‖)
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro source _hsource
        by_cases hsame : regions.SameTerminalBlock source target
        · rw [if_pos hsame]
        · rw [if_neg hsame,
            regions.generatedCountingMass_single_apply_eq_zero hd hM rho
              spacing epsilon background chain fineSmall source target
              (phi source) hsame,
            norm_zero]
    _ ≤ (∑ _source ∈ fibre,
        (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) * C) := by
      apply Finset.sum_le_sum
      intro source hsource
      have hsame : regions.SameTerminalBlock source target :=
        (Finset.mem_filter.mp hsource).2
      rw [regions.norm_generatedCountingMass_single_apply_of_same hd hM rho
        spacing epsilon background chain fineSmall source target
        (phi source) hsame]
      exact mul_le_mul_of_nonneg_left (hphi source hsame)
        (pow_nonneg hw _)
    _ = (fibre.card : ℝ) *
        ((cmp99SourceBlockAverageWeight M d) ^ (2 * depth) * C) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((M ^ depth) ^ d : ℕ) : ℝ) *
        ((cmp99SourceBlockAverageWeight M d) ^ (2 * depth) * C) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast regions.card_sameTerminalBlock_le target
      · exact hterm_nonneg
    _ = (cmp99SourceBlockAverageWeight M d) ^ depth * C := by
      rw [← mul_assoc, cmp99GeneratedTerminalBlockCount_mul_weight_sq]

end

end YangMills.RG
