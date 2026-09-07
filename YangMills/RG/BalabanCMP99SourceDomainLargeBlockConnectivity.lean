/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCellDomains
import YangMills.RG.BalabanCMP99SourcePi4CollarDomain

/-!
# Connectivity of literal CMP99 large-block carriers

A CMP99 source domain is connected on the lattice of source cells.  Its
literal carrier is the union of the sixteen order-two large blocks owned by
each source cell.  This file proves that the carrier itself is connected in
the large-block face graph.

The proof is constructive.  Each order-two fibre is joined to its lower
corner coordinate by coordinate.  Adjacent source cells are joined by the
two corresponding large-block face steps.  Consequently a source-cell walk
lifts to a large-block walk whose support remains in the literal carrier.
-/

namespace YangMills.RG

noncomputable section

/-- Replace the first `n` coordinates of the lower corner by those of a
target large block. -/
def cmp99SourceBaseCellPrefix {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (target : FinBox 4 (2 * Q)) (n : ℕ) :
    FinBox 4 (2 * Q) :=
  fun i =>
    if i.val < n then target i
    else cmp116BlockCorner (M := 2) cell i

@[simp] theorem cmp99SourceBaseCellPrefix_zero {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (target : FinBox 4 (2 * Q)) :
    cmp99SourceBaseCellPrefix cell target 0 =
      cmp116BlockCorner (M := 2) cell := by
  funext i
  simp [cmp99SourceBaseCellPrefix]

@[simp] theorem cmp99SourceBaseCellPrefix_four {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (target : FinBox 4 (2 * Q)) :
    cmp99SourceBaseCellPrefix cell target 4 = target := by
  funext i
  simp [cmp99SourceBaseCellPrefix, i.isLt]

theorem mem_cmp99SourceBaseCellPrefix {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (target : FinBox 4 (2 * Q))
    (htarget : target ∈ cmp99SourceBaseCell cell) (n : ℕ) :
    cmp99SourceBaseCellPrefix cell target n ∈
      cmp99SourceBaseCell cell := by
  rw [mem_cmp99SourceBaseCell_iff] at htarget ⊢
  change blockSite 2 Q target = cell at htarget
  change blockSite 2 Q (cmp99SourceBaseCellPrefix cell target n) = cell
  rw [blockSite_eq_iff_cube] at htarget ⊢
  intro i
  by_cases hi : i.val < n
  · simpa [cmp99SourceBaseCellPrefix, hi] using htarget i
  · simp only [cmp99SourceBaseCellPrefix, if_neg hi, cmp116BlockCorner]
    exact ⟨by omega, by omega⟩

theorem cmp99SourceBaseCellPrefix_next_eq_replace {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (target : FinBox 4 (2 * Q))
    (n : ℕ) (hn : n < 4) :
    cmp99SourceBaseCellPrefix cell target (n + 1) =
      cmp99ReplaceCoord (cmp99SourceBaseCellPrefix cell target n)
        ⟨n, hn⟩ (target ⟨n, hn⟩) := by
  funext j
  by_cases hj : j = ⟨n, hn⟩
  · subst j
    simp [cmp99SourceBaseCellPrefix, cmp99ReplaceCoord]
  · have hjval : j.val ≠ n := by
      intro hval
      exact hj (Fin.ext hval)
    by_cases hjn : j.val < n
    · simp [cmp99SourceBaseCellPrefix, cmp99ReplaceCoord, hj, hjn,
        Nat.lt_succ_of_lt hjn]
    · have hjnext : ¬ j.val < n + 1 := by omega
      simp [cmp99SourceBaseCellPrefix, cmp99ReplaceCoord, hj, hjn, hjnext]

theorem cmp99SourceBaseCellPrefix_apply_next {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (target : FinBox 4 (2 * Q))
    (n : ℕ) (hn : n < 4) :
    cmp99SourceBaseCellPrefix cell target n ⟨n, hn⟩ =
      cmp116BlockCorner (M := 2) cell ⟨n, hn⟩ := by
  simp [cmp99SourceBaseCellPrefix]

/-- One coordinate phase from the lower corner to a member of an order-two
fibre stays inside that same fibre. -/
theorem exists_cmp99SourceBaseCellPrefix_stepWalk {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (target : FinBox 4 (2 * Q))
    (htarget : target ∈ cmp99SourceBaseCell cell)
    (n : ℕ) (hn : n < 4) :
    ∃ w : (cmp116CoarseFaceAdj 4 (2 * Q)).Walk
        (cmp99SourceBaseCellPrefix cell target n)
        (cmp99SourceBaseCellPrefix cell target (n + 1)),
      ∀ v ∈ w.support, v ∈ cmp99SourceBaseCell cell := by
  let i : Fin 4 := ⟨n, hn⟩
  let x := cmp99SourceBaseCellPrefix cell target n
  have hx : x ∈ cmp99SourceBaseCell cell :=
    mem_cmp99SourceBaseCellPrefix cell target htarget n
  have hxi : x i = cmp116BlockCorner (M := 2) cell i :=
    cmp99SourceBaseCellPrefix_apply_next cell target n hn
  have htargetCube :
      2 * (cell i).val ≤ (target i).val ∧
        (target i).val < 2 * (cell i).val + 2 := by
    exact
      ((blockSite_eq_iff_cube 2 Q target cell).mp
        ((mem_cmp99SourceBaseCell_iff cell target).mp htarget)) i
  have hend :
      cmp99SourceBaseCellPrefix cell target (n + 1) =
        cmp99ReplaceCoord x i (target i) :=
    cmp99SourceBaseCellPrefix_next_eq_replace cell target n hn
  by_cases heq : target i = x i
  · have hreplace : cmp99ReplaceCoord x i (target i) = x := by
      rw [heq]
      exact cmp99ReplaceCoord_self x i
    rw [hend, hreplace]
    exact ⟨SimpleGraph.Walk.nil, by
      intro v hv
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      subst v
      exact hx⟩
  · have hsucc : target i = cmp99CyclicSucc (x i) := by
      apply Fin.ext
      have hcornerVal :
          (x i).val = 2 * (cell i).val := by
        rw [hxi]
        rfl
      have htargetVal : (target i).val = (x i).val + 1 := by
        have hneVal : (target i).val ≠ (x i).val := by
          intro h
          exact heq (Fin.ext h)
        omega
      rw [htargetVal]
      simp only [cmp99CyclicSucc]
      rw [Nat.mod_eq_of_lt]
      rw [hcornerVal]
      have hcell := (cell i).isLt
      omega
    rw [hend, hsucc, cmp99ReplaceCoord_succ]
    obtain ⟨w, hw⟩ := exists_cmp116CoarseFaceShiftWalk x i
    refine ⟨w, ?_⟩
    intro v hv
    rcases hw v hv with rfl | rfl
    · exact hx
    · simpa [← cmp99ReplaceCoord_succ x i, ← hsucc, ← hend] using
        mem_cmp99SourceBaseCellPrefix cell target htarget (n + 1)

/-- Every large block in a source base cell is connected to that cell's
lower corner inside the same literal sixteen-block fibre. -/
theorem exists_cmp99SourceBaseCell_walk_from_corner {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (target : FinBox 4 (2 * Q))
    (htarget : target ∈ cmp99SourceBaseCell cell) :
    ∃ w : (cmp116CoarseFaceAdj 4 (2 * Q)).Walk
        (cmp116BlockCorner (M := 2) cell) target,
      ∀ v ∈ w.support, v ∈ cmp99SourceBaseCell cell := by
  obtain ⟨w₀, hw₀⟩ :=
    exists_cmp99SourceBaseCellPrefix_stepWalk cell target htarget 0 (by omega)
  obtain ⟨w₁, hw₁⟩ :=
    exists_cmp99SourceBaseCellPrefix_stepWalk cell target htarget 1 (by omega)
  obtain ⟨w₂, hw₂⟩ :=
    exists_cmp99SourceBaseCellPrefix_stepWalk cell target htarget 2 (by omega)
  obtain ⟨w₃, hw₃⟩ :=
    exists_cmp99SourceBaseCellPrefix_stepWalk cell target htarget 3 (by omega)
  let raw := ((w₀.append w₁).append w₂).append w₃
  let w : (cmp116CoarseFaceAdj 4 (2 * Q)).Walk
      (cmp116BlockCorner (M := 2) cell) target :=
    raw.copy (cmp99SourceBaseCellPrefix_zero cell target)
      (cmp99SourceBaseCellPrefix_four cell target)
  refine ⟨w, ?_⟩
  intro v hv
  have hv' : v ∈ raw.support := by
    simpa [w, SimpleGraph.Walk.support_copy] using hv
  dsimp only [raw] at hv'
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv'
  rcases hv' with hv' | hv'
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hv'
    rcases hv' with hv' | hv'
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hv'
      rcases hv' with hv' | hv'
      · exact hw₀ v hv'
      · exact hw₁ v hv'
    · exact hw₂ v hv'
  · exact hw₃ v hv'

/-- The lower corner belongs to its literal order-two source fibre. -/
theorem cmp116BlockCorner_mem_cmp99SourceBaseCell {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    cmp116BlockCorner (M := 2) cell ∈ cmp99SourceBaseCell cell := by
  rw [mem_cmp99SourceBaseCell_iff]
  exact blockSite_cmp116BlockCorner cell

/-- The first fine face step from a source-cell lower corner remains in the
same order-two fibre. -/
theorem shift_cmp116BlockCorner_mem_cmp99SourceBaseCell
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) (i : Fin 4) :
    FinBox.shift (cmp116BlockCorner (M := 2) cell) i ∈
      cmp99SourceBaseCell cell := by
  rw [mem_cmp99SourceBaseCell_iff]
  change blockSite 2 Q
      (FinBox.shift (cmp116BlockCorner (M := 2) cell) i) = cell
  rw [blockSite_eq_iff_cube]
  intro j
  by_cases hji : j = i
  · subst j
    simp only [FinBox.shift, if_pos, cmp116BlockCorner]
    rw [Nat.mod_eq_of_lt]
    · exact ⟨by omega, by omega⟩
    · have hcell := (cell i).isLt
      omega
  · simp only [FinBox.shift, if_neg hji, cmp116BlockCorner]
    exact ⟨by omega, by omega⟩

/-- Two fine face steps lift one forward source-cell face step. -/
theorem exists_cmp99SourceBaseCell_cornerWalk_shift
    {Q : ℕ} [NeZero Q] (left : FinBox 4 Q) (i : Fin 4) :
    ∃ w : (cmp116CoarseFaceAdj 4 (2 * Q)).Walk
        (cmp116BlockCorner (M := 2) left)
        (cmp116BlockCorner (M := 2) (FinBox.shift left i)),
      ∀ v ∈ w.support,
        v ∈ cmp99SourceBaseCell left ∪
          cmp99SourceBaseCell (FinBox.shift left i) := by
  let corner := cmp116BlockCorner (M := 2) left
  obtain ⟨w₀, hw₀⟩ := exists_cmp116CoarseFaceShiftWalk corner i
  obtain ⟨w₁, hw₁⟩ :=
    exists_cmp116CoarseFaceShiftWalk (FinBox.shift corner i) i
  have hend :
      cmp116BlockCorner (M := 2) (FinBox.shift left i) =
        FinBox.shift (FinBox.shift corner i) i := by
    rw [cmp116BlockCorner_shift]
    rfl
  let raw := w₀.append w₁
  let w : (cmp116CoarseFaceAdj 4 (2 * Q)).Walk
      (cmp116BlockCorner (M := 2) left)
      (cmp116BlockCorner (M := 2) (FinBox.shift left i)) :=
    raw.copy rfl hend.symm
  refine ⟨w, ?_⟩
  intro v hv
  have hv' : v ∈ raw.support := by
    simpa [w, SimpleGraph.Walk.support_copy] using hv
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv'
  rcases hv' with hv' | hv'
  · rcases hw₀ v hv' with rfl | rfl
    · exact Finset.mem_union_left _
        (cmp116BlockCorner_mem_cmp99SourceBaseCell left)
    · exact Finset.mem_union_left _
        (shift_cmp116BlockCorner_mem_cmp99SourceBaseCell left i)
  · rcases hw₁ v hv' with rfl | rfl
    · exact Finset.mem_union_left _
        (shift_cmp116BlockCorner_mem_cmp99SourceBaseCell left i)
    · rw [← hend]
      exact Finset.mem_union_right _
        (cmp116BlockCorner_mem_cmp99SourceBaseCell (FinBox.shift left i))

/-- Lower corners of face-adjacent source cells are joined by two large-block
face steps, with support contained in the union of the two source fibres. -/
theorem exists_cmp99SourceBaseCell_cornerWalk_of_adj
    {Q : ℕ} [NeZero Q] {left right : FinBox 4 Q}
    (hadj : (cmp116CoarseFaceAdj 4 Q).Adj left right) :
    ∃ w : (cmp116CoarseFaceAdj 4 (2 * Q)).Walk
        (cmp116BlockCorner (M := 2) left)
        (cmp116BlockCorner (M := 2) right),
      ∀ v ∈ w.support,
        v ∈ cmp99SourceBaseCell left ∪ cmp99SourceBaseCell right := by
  rcases hadj.2 with ⟨i, hforward | hbackward⟩
  · subst right
    exact exists_cmp99SourceBaseCell_cornerWalk_shift left i
  · subst left
    obtain ⟨w, hw⟩ :=
      exists_cmp99SourceBaseCell_cornerWalk_shift right i
    refine ⟨w.reverse, ?_⟩
    intro v hv
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
    have hv' := hw v hv
    simpa [Finset.union_comm] using hv'

/-- A source-cell face walk lifts to a large-block face walk through the
literal carrier of the source domain. -/
theorem exists_cmp99SourceDomainLargeBlocks_cornerWalk
    {Q S : ℕ} [NeZero Q]
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)
    {left right : FinBox 4 Q}
    (w : (cmp116CoarseFaceAdj 4 Q).Walk left right)
    (hw : ∀ cell ∈ w.support, cell ∈ X.blocks) :
    ∃ lifted : (cmp116CoarseFaceAdj 4 (2 * Q)).Walk
        (cmp116BlockCorner (M := 2) left)
        (cmp116BlockCorner (M := 2) right),
      ∀ block ∈ lifted.support,
        block ∈ cmp99SourceDomainLargeBlocks X := by
  induction w with
  | @nil u =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro block hblock
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hblock
      subst block
      rw [mem_cmp99SourceDomainLargeBlocks_iff]
      have hleft : u ∈ X.blocks := hw u (by simp)
      simpa [cmp99SourceBaseCellOwner,
        blockSite_cmp116BlockCorner] using hleft
  | @cons u v t huv p ih =>
      have hu : u ∈ X.blocks := hw u (by simp)
      have hv : v ∈ X.blocks := hw v (by simp)
      have hp : ∀ cell ∈ p.support, cell ∈ X.blocks := by
        intro cell hcell
        exact hw cell (by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ hcell)
      obtain ⟨bridge, hbridge⟩ :=
        exists_cmp99SourceBaseCell_cornerWalk_of_adj huv
      obtain ⟨tail, htail⟩ := ih hp
      refine ⟨bridge.append tail, ?_⟩
      intro block hblock
      rw [SimpleGraph.Walk.mem_support_append_iff] at hblock
      rcases hblock with hblock | hblock
      · rcases Finset.mem_union.mp (hbridge block hblock) with hleft | hright
        · rw [mem_cmp99SourceDomainLargeBlocks_iff]
          rw [mem_cmp99SourceBaseCell_iff] at hleft
          simpa [hleft] using hu
        · rw [mem_cmp99SourceDomainLargeBlocks_iff]
          rw [mem_cmp99SourceBaseCell_iff] at hright
          simpa [hright] using hv
      · exact htail block hblock

/-- The literal large-block carrier of every source simple domain is
face-connected.  No extra connectedness hypothesis is required beyond the
source-domain certificate itself. -/
theorem walkConnected_cmp99SourceDomainLargeBlocks
    {Q S : ℕ} [NeZero Q]
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    walkConnected (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp99SourceDomainLargeBlocks X) := by
  obtain ⟨root, hroot⟩ := X.nonempty
  let rootCorner := cmp116BlockCorner (M := 2) root
  exact walkConnected_of_walk_from_root
    (cmp116CoarseFaceAdj 4 (2 * Q))
    (cmp99SourceDomainLargeBlocks X) rootCorner (by
      intro target htarget
      have howner :
          cmp99SourceBaseCellOwner target ∈ X.blocks :=
        (mem_cmp99SourceDomainLargeBlocks_iff X target).mp htarget
      obtain ⟨coarseWalk, hcoarseWalk⟩ :=
        X.connected root hroot (cmp99SourceBaseCellOwner target) howner
      obtain ⟨lifted, hlifted⟩ :=
        exists_cmp99SourceDomainLargeBlocks_cornerWalk X coarseWalk
          hcoarseWalk
      obtain ⟨fiberWalk, hfiberWalk⟩ :=
        exists_cmp99SourceBaseCell_walk_from_corner
          (cmp99SourceBaseCellOwner target) target
          (mem_cmp99SourceBaseCell_owner target)
      refine ⟨lifted.append fiberWalk, ?_⟩
      intro block hblock
      rw [SimpleGraph.Walk.mem_support_append_iff] at hblock
      rcases hblock with hblock | hblock
      · exact hlifted block hblock
      · rw [mem_cmp99SourceDomainLargeBlocks_iff]
        have hbase := hfiberWalk block hblock
        rw [mem_cmp99SourceBaseCell_iff] at hbase
        simpa [hbase] using howner)

/-- A nonempty source-cell domain has a nonempty literal large-block
carrier. -/
theorem nonempty_cmp99SourceDomainLargeBlocks
    {Q S : ℕ} [NeZero Q]
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    (cmp99SourceDomainLargeBlocks X).Nonempty := by
  obtain ⟨cell, hcell⟩ := X.nonempty
  refine ⟨cmp116BlockCorner (M := 2) cell, ?_⟩
  rw [mem_cmp99SourceDomainLargeBlocks_iff]
  simpa [cmp99SourceBaseCellOwner,
    blockSite_cmp116BlockCorner] using hcell

end

end YangMills.RG
