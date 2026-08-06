/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCountingMassOutputRow

/-!
# Generated counting mass on source-dependent fibre values

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

The third species of CMP99 (3.88) fixes an output site and applies the
normalized `Q'^* Q'` kernel to Green values which vary with the input site.
The already sealed fixed-output row theorem cannot be used directly because
its quantified fibre vector is common to every input coordinate.

This file proves the source-faithful replacement.  A terminal fibre contains
at most `(M^depth)^d` sites, while every nonzero generated counting-mass block
has the exact norm `(M^{-d})^(2*depth)`.  The block count therefore cancels
one copy of the normalization before any regional-cell sum.  No range-ball
cardinality or abstract adjoint argument is introduced.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Coordinatewise residue inside the literal order-`M^depth` terminal
block.  On one terminal-owner fibre this map is injective. -/
def cmp99GeneratedTerminalBlockResidue
    (M N depth : ℕ) [NeZero M]
    (x : FinBox d (cmp99RegionalLatticeSize M N depth)) :
    FinBox d (M ^ depth) :=
  fun i => ⟨(x i).val % M ^ depth,
    Nat.mod_lt _ (pow_pos (NeZero.pos M) depth)⟩

/-- Two fine sites with the same terminal owner are determined by their
residues inside that owner block. -/
theorem cmp99GeneratedTerminalBlockResidue_injOn_owner
    (depth : ℕ)
    (x y : FinBox d (cmp99RegionalLatticeSize M N depth))
    (howner : cmp99GeneratedTerminalBlockSite M N depth x =
      cmp99GeneratedTerminalBlockSite M N depth y)
    (hresidue : cmp99GeneratedTerminalBlockResidue M N depth x =
      cmp99GeneratedTerminalBlockResidue M N depth y) :
    x = y := by
  funext i
  apply Fin.ext
  have hquot : (x i).val / M ^ depth = (y i).val / M ^ depth := by
    exact congrArg Fin.val (congrFun howner i)
  have hrem : (x i).val % M ^ depth = (y i).val % M ^ depth := by
    exact congrArg Fin.val (congrFun hresidue i)
  have hxdiv : (x i).val = M ^ depth * ((x i).val / M ^ depth) +
      (x i).val % M ^ depth := (Nat.div_add_mod _ _).symm
  have hydiv : (y i).val = M ^ depth * ((y i).val / M ^ depth) +
      (y i).val % M ^ depth := (Nat.div_add_mod _ _).symm
  omega

/-- A terminal-owner fibre of a canonical generated region chain contains at
most the literal block volume `(M^depth)^d`, independently of the ambient
volume and of the active-region shape. -/
theorem card_cmp99SourceIteratedLift_sameTerminalBlock_le
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth)) :
    (Finset.univ.filter fun source =>
      (cmp99SourceIteratedLiftActiveRegionChain
        (M := M) Omega depth).SameTerminalBlock source target).card ≤
      (M ^ depth) ^ d := by
  classical
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
  let residue : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth) →
      FinBox d (M ^ depth) :=
    fun source => cmp99GeneratedTerminalBlockResidue M N depth source.1
  have hinj : Set.InjOn residue
      {source | regions.SameTerminalBlock source target} := by
    intro source hsource target' htarget' heq
    apply Subtype.ext
    apply cmp99GeneratedTerminalBlockResidue_injOn_owner
      (M := M) (N := N) depth source.1 target'.1
    · have hs := (cmp99SourceIteratedLift_sameTerminalBlock_iff
          (M := M) Omega depth source target).1 hsource
      have ht := (cmp99SourceIteratedLift_sameTerminalBlock_iff
          (M := M) Omega depth target' target).1 htarget'
      exact hs.trans ht.symm
    · exact heq
  calc
    (Finset.univ.filter fun source =>
        regions.SameTerminalBlock source target).card ≤
        (Finset.univ : Finset (FinBox d (M ^ depth))).card := by
      apply Finset.card_le_card_of_injOn residue
      · intro source _hsource
        exact Finset.mem_univ _
      · intro source hsource target' htarget' heq
        apply hinj
        · simpa using (Finset.mem_filter.mp hsource).2
        · simpa using (Finset.mem_filter.mp htarget').2
        · exact heq
    _ = (M ^ depth) ^ d := by
      simp

/-- Exact scalar cancellation behind the source-normalized terminal row:
one terminal block count cancels one of the two averaging weights. -/
theorem cmp99GeneratedTerminalBlockCount_mul_weight_sq
    (M d depth : ℕ) [NeZero M] :
    (((M ^ depth) ^ d : ℕ) : ℝ) *
        (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) =
      (cmp99SourceBlockAverageWeight M d) ^ depth := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      have hcount : ((((M ^ (depth + 1)) ^ d : ℕ) : ℝ)) =
          (((M ^ depth) ^ d : ℕ) : ℝ) * (M : ℝ) ^ d := by
        push_cast
        rw [pow_succ, mul_pow]
      have hweight :
          (cmp99SourceBlockAverageWeight M d) ^ (2 * (depth + 1)) =
            (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) *
              (cmp99SourceBlockAverageWeight M d *
                cmp99SourceBlockAverageWeight M d) := by
        rw [show 2 * (depth + 1) = 2 * depth + 2 by omega,
          pow_add, pow_two]
      rw [hcount, hweight, pow_succ]
      calc
        ((((M ^ depth) ^ d : ℕ) : ℝ) * (M : ℝ) ^ d) *
            ((cmp99SourceBlockAverageWeight M d) ^ (2 * depth) *
              (cmp99SourceBlockAverageWeight M d *
                cmp99SourceBlockAverageWeight M d)) =
          ((((M ^ depth) ^ d : ℕ) : ℝ) *
              (cmp99SourceBlockAverageWeight M d) ^ (2 * depth)) *
            (((M : ℝ) ^ d) * cmp99SourceBlockAverageWeight M d) *
              cmp99SourceBlockAverageWeight M d := by ring
        _ = (cmp99SourceBlockAverageWeight M d) ^ depth *
            cmp99SourceBlockAverageWeight M d := by
          rw [ih, card_mul_cmp99SourceBlockAverageWeight]
          ring
        _ = (cmp99SourceBlockAverageWeight M d) ^ (depth + 1) := by
          rw [pow_succ]

/-- Source-dependent fixed-output sum for the literal generated counting
mass.  The varying values are controlled only on the actual terminal fibre;
outside it the generated kernel vanishes exactly. -/
theorem cmp99SourceIteratedLift_sum_norm_generatedCountingMass_varying_le
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
    (phi : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth) (SUNLieCoord Nc))
    (C : ℝ) (hC : 0 ≤ C)
    (hphi : ∀ source,
      (cmp99SourceIteratedLiftActiveRegionChain
        (M := M) Omega depth).SameTerminalBlock source target →
      ‖phi source‖ ≤ C) :
    (∑ source,
        ‖(cmp99SourceIteratedLiftActiveRegionChain
            (M := M) Omega depth).generatedCountingMass hd hM rho
          spacing epsilon background chain fineSmall
          (singleFinitePiLp source (phi source)) target‖) ≤
      (cmp99SourceBlockAverageWeight M d) ^ depth * C := by
  classical
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
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
      (∑ source in fibre,
        ‖regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp source (phi source)) target‖) := by
        change (∑ source,
            ‖regions.generatedCountingMass hd hM rho spacing epsilon background
              chain fineSmall (singleFinitePiLp source (phi source)) target‖) =
          ∑ source in Finset.univ.filter (fun source =>
            regions.SameTerminalBlock source target),
            ‖regions.generatedCountingMass hd hM rho spacing epsilon background
              chain fineSmall (singleFinitePiLp source (phi source)) target‖
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
    _ ≤ (∑ _source in fibre,
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
      · exact_mod_cast card_cmp99SourceIteratedLift_sameTerminalBlock_le
          (M := M) Omega depth target
      · exact hterm_nonneg
    _ = (cmp99SourceBlockAverageWeight M d) ^ depth * C := by
      rw [← mul_assoc, cmp99GeneratedTerminalBlockCount_mul_weight_sq]

end

end YangMills.RG
