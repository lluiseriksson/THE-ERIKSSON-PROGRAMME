/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceConcentricShell

/-!
# Source-faithful geometry of the CMP99 `Omega_n(Pi)` sequence

Printed p. 408 defines a sequence indexed by `n = 0, ..., j+1`: there are
exactly `j+2` domains.  Its distinguished penultimate member is
`Omega_j(Pi) = tilde Pi^4`; the final member `Omega_{j+1}` is the smaller
intersection introduced immediately before that equality.  The largest
member satisfies `Omega_0(Pi) ⊆ tilde Pi^5`.

This distinction matters for shells.  For `r < j`,
`Omega_r \ Omega_{r+1}` lies in the outer shell
`tilde Pi^5 \ tilde Pi^4`.  The final transition
`Omega_j \ Omega_{j+1}` instead lies *inside* `tilde Pi^4`.  This file records
and proves exactly those consequences, avoiding the false assertion that
every transition shell lies outside `tilde Pi^4`.

Only geometry is represented.  The boundary-value operators `G'_Pi` and
`C_Pi` are not fields of this structure and are not identified with any
hard-support inverse.
-/

namespace YangMills.RG

noncomputable section

/-- Index zero in the source sequence of length `j+2`. -/
def cmp99OmegaZeroIndex (j : ℕ) : Fin (j + 2) := ⟨0, by omega⟩

/-- The distinguished source index `j`, where `Omega_j = tilde Pi^4`. -/
def cmp99OmegaPi4Index (j : ℕ) : Fin (j + 2) := ⟨j, by omega⟩

/-- The final source index `j+1`. -/
def cmp99OmegaLastIndex (j : ℕ) : Fin (j + 2) := ⟨j + 1, by omega⟩

/-- Embed an outer-transition index `r < j` in the full source sequence. -/
def cmp99OmegaOuterIndex {j : ℕ} (r : Fin j) : Fin (j + 2) :=
  ⟨r.val, by omega⟩

/-- The successor of an outer-transition index. -/
def cmp99OmegaOuterNextIndex {j : ℕ} (r : Fin j) : Fin (j + 2) :=
  ⟨r.val + 1, by omega⟩

/-- Embed any of the `j+1` consecutive transitions in the sequence. -/
def cmp99OmegaTransitionIndex {j : ℕ} (r : Fin (j + 1)) : Fin (j + 2) :=
  ⟨r.val, by omega⟩

/-- Successor index of a consecutive transition. -/
def cmp99OmegaTransitionNextIndex {j : ℕ}
    (r : Fin (j + 1)) : Fin (j + 2) :=
  ⟨r.val + 1, by omega⟩

/-- The literal geometric data of a CMP99 source sequence.  A `Fin (j+2)`
family makes the printed count part of the type rather than a side condition
on an untyped list. -/
structure CMP99SourceOmegaGeometry {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (j : ℕ) where
  regions : Fin (j + 2) → Finset (FinBox 4 (2 * Q))
  nested : ∀ {r s : Fin (j + 2)}, r ≤ s → regions s ⊆ regions r
  omega_j_eq_pi4 : regions (cmp99OmegaPi4Index j) =
    cmp99SourceTildePiLargeBlocks cell 4
  omega_zero_subset_pi5 : regions (cmp99OmegaZeroIndex j) ⊆
    cmp99SourceTildePiLargeBlocks cell 5

namespace CMP99SourceOmegaGeometry

/-- List view of the typed sequence, useful for source-facing iteration. -/
def regionsList {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) :
    List (Finset (FinBox 4 (2 * Q))) :=
  List.ofFn Seq.regions

@[simp] theorem length_regionsList {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) :
    Seq.regionsList.length = j + 2 := by
  simp [regionsList]

/-- Every source region lies in the printed `tilde Pi^5` envelope. -/
theorem region_subset_pi5 {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    Seq.regions r ⊆ cmp99SourceTildePiLargeBlocks cell 5 := by
  intro block hblock
  apply Seq.omega_zero_subset_pi5
  apply Seq.nested (r := cmp99OmegaZeroIndex j) (s := r)
  · change 0 ≤ r.val
    omega
  · exact hblock

/-- Consequently every source region also lies in the larger p. 415 cube
`tilde Pi^8`. -/
theorem region_subset_pi8 {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    Seq.regions r ⊆ cmp99SourceTildePiLargeBlocks cell 8 :=
  fun _ h => cmp99SourceTildePi5LargeBlocks_subset_pi8 cell
    (Seq.region_subset_pi5 r h)

/-- `tilde Pi^4 = Omega_j` is contained in the initial region. -/
theorem pi4_subset_omega_zero {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) :
    cmp99SourceTildePiLargeBlocks cell 4 ⊆
      Seq.regions (cmp99OmegaZeroIndex j) := by
  rw [← Seq.omega_j_eq_pi4]
  exact Seq.nested (by
    change 0 ≤ j
    omega)

/-- The transition shell `Omega_r \ Omega_{r+1}` for `r < j`. -/
noncomputable def outerTransitionShell {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin j) :
    Finset (FinBox 4 (2 * Q)) :=
  Seq.regions (cmp99OmegaOuterIndex r) \
    Seq.regions (cmp99OmegaOuterNextIndex r)

@[simp] theorem mem_outerTransitionShell_iff {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin j)
    (block : FinBox 4 (2 * Q)) :
    block ∈ Seq.outerTransitionShell r ↔
      block ∈ Seq.regions (cmp99OmegaOuterIndex r) ∧
        block ∉ Seq.regions (cmp99OmegaOuterNextIndex r) := by
  simp [outerTransitionShell]

/-- Every outer transition lies in the literal one-block source shell
`tilde Pi^5 \ tilde Pi^4`. -/
theorem outerTransitionShell_subset_pi4Pi5Shell
    {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin j) :
    Seq.outerTransitionShell r ⊆
      cmp99SourcePi4Pi5LargeBlockShell cell := by
  intro block hblock
  rw [mem_outerTransitionShell_iff] at hblock
  rw [mem_cmp99SourcePi4Pi5LargeBlockShell_iff]
  refine ⟨Seq.region_subset_pi5 _ hblock.1, ?_⟩
  intro hpi4
  have hj : block ∈ Seq.regions (cmp99OmegaPi4Index j) := by
    rw [Seq.omega_j_eq_pi4]
    exact hpi4
  apply hblock.2
  apply Seq.nested (r := cmp99OmegaOuterNextIndex r)
      (s := cmp99OmegaPi4Index j)
  · change r.val + 1 ≤ j
    exact r.isLt
  · exact hj

/-- Uniform cardinality bound for each outer transition, valid with periodic
wraparound. -/
theorem card_outerTransitionShell_le {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin j) :
    (Seq.outerTransitionShell r).card ≤ 20736 :=
  (Finset.card_le_card (Seq.outerTransitionShell_subset_pi4Pi5Shell r)).trans
    (card_cmp99SourcePi4Pi5LargeBlockShell_le cell)

/-- Sharp no-wrap cardinality budget for every outer transition. -/
theorem card_outerTransitionShell_le_exactEnvelope {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin j)
    (hfit : 12 ≤ 2 * Q) :
    (Seq.outerTransitionShell r).card ≤ 10736 :=
  (Finset.card_le_card (Seq.outerTransitionShell_subset_pi4Pi5Shell r)).trans_eq
    (card_cmp99SourcePi4Pi5LargeBlockShell_eq cell hfit)

/-- The distinct final shell `Omega_j \ Omega_{j+1}`. -/
noncomputable def terminalTransitionShell {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) :
    Finset (FinBox 4 (2 * Q)) :=
  Seq.regions (cmp99OmegaPi4Index j) \
    Seq.regions (cmp99OmegaLastIndex j)

/-- Unlike the outer transitions, the final transition lies inside
`tilde Pi^4`. -/
theorem terminalTransitionShell_subset_pi4 {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) :
    Seq.terminalTransitionShell ⊆
      cmp99SourceTildePiLargeBlocks cell 4 := by
  intro block hblock
  have hleft : block ∈ Seq.regions (cmp99OmegaPi4Index j) :=
    (Finset.mem_sdiff.mp hblock).1
  rw [Seq.omega_j_eq_pi4] at hleft
  exact hleft

/-- Uniform cardinality budget for the final, inner transition. -/
theorem card_terminalTransitionShell_le {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) :
    Seq.terminalTransitionShell.card ≤ 10000 :=
  (Finset.card_le_card Seq.terminalTransitionShell_subset_pi4).trans
    (card_cmp99SourceTildePi4LargeBlocks_le cell)

/-- Any of the `j+1` consecutive transition shells. -/
noncomputable def transitionShell {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    Finset (FinBox 4 (2 * Q)) :=
  Seq.regions (cmp99OmegaTransitionIndex r) \
    Seq.regions (cmp99OmegaTransitionNextIndex r)

@[simp] theorem mem_transitionShell_iff {Q : ℕ} [NeZero Q]
    {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (block : FinBox 4 (2 * Q)) :
    block ∈ Seq.transitionShell r ↔
      block ∈ Seq.regions (cmp99OmegaTransitionIndex r) ∧
        block ∉ Seq.regions (cmp99OmegaTransitionNextIndex r) := by
  simp [transitionShell]

/-- Exact telescopic decomposition of the initial region into the final
region and all consecutive shells.  This is a set identity; later operator
resolvent expansions can index their insertions by the same `Fin (j+1)`
family without changing the source count. -/
theorem omega_zero_eq_last_union_transitionShells
    {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q} {j : ℕ}
    (Seq : CMP99SourceOmegaGeometry cell j) :
    Seq.regions (cmp99OmegaZeroIndex j) =
      Seq.regions (cmp99OmegaLastIndex j) ∪
        (Finset.univ : Finset (Fin (j + 1))).biUnion Seq.transitionShell := by
  classical
  ext block
  constructor
  · intro hzero
    rw [Finset.mem_union]
    by_cases hlast : block ∈ Seq.regions (cmp99OmegaLastIndex j)
    · exact Or.inl hlast
    · right
      let p : ℕ → Prop := fun k =>
        ∃ hk : k < j + 2,
          block ∉ Seq.regions (⟨k, hk⟩ : Fin (j + 2))
      have hex : ∃ k, p k := by
        refine ⟨j + 1, ⟨by omega, ?_⟩⟩
        simpa [cmp99OmegaLastIndex] using hlast
      let k := Nat.find hex
      have hkSpec : p k := Nat.find_spec hex
      obtain ⟨hklt, hknot⟩ := hkSpec
      have hkpos : 0 < k := by
        by_contra hkzero
        have hkeq : k = 0 := by omega
        subst k
        apply hknot
        have hidx : (⟨Nat.find hex, hklt⟩ : Fin (j + 2)) =
            cmp99OmegaZeroIndex j := Fin.ext hkeq
        rw [hidx]
        exact hzero
      let r : Fin (j + 1) := ⟨k - 1, by omega⟩
      rw [Finset.mem_biUnion]
      refine ⟨r, Finset.mem_univ _, ?_⟩
      rw [mem_transitionShell_iff]
      constructor
      · by_contra hprev
        have hpPrev : p (k - 1) := by
          refine ⟨by omega, ?_⟩
          simpa [r, cmp99OmegaTransitionIndex] using hprev
        have hminimal : k ≤ k - 1 := Nat.find_min' hex hpPrev
        omega
      · intro hnext
        apply hknot
        have hidx : (⟨k, hklt⟩ : Fin (j + 2)) =
            cmp99OmegaTransitionNextIndex r := by
          apply Fin.ext
          simp [r, cmp99OmegaTransitionNextIndex]
          omega
        rw [hidx]
        exact hnext
  · intro hright
    rw [Finset.mem_union] at hright
    rcases hright with hlast | hshell
    · apply Seq.nested (r := cmp99OmegaZeroIndex j)
        (s := cmp99OmegaLastIndex j)
      · change 0 ≤ j + 1
        omega
      · exact hlast
    · rw [Finset.mem_biUnion] at hshell
      obtain ⟨r, -, hr⟩ := hshell
      rw [mem_transitionShell_iff] at hr
      apply Seq.nested (r := cmp99OmegaZeroIndex j)
          (s := cmp99OmegaTransitionIndex r)
      · change 0 ≤ r.val
        omega
      · exact hr.1

end CMP99SourceOmegaGeometry

end

end YangMills.RG
