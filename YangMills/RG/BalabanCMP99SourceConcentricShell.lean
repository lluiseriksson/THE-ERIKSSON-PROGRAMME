/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceConcentricLargeBlockCube

/-!
# The literal CMP99 shell between `tilde Pi^4` and `tilde Pi^5`

Printed p. 408 constructs the localization sequence with
`Omega_j(Pi) = tilde Pi^4` and proves that its largest member satisfies
`Omega_0(Pi) ⊆ tilde Pi^5`.  Thus the one-large-block envelope
`tilde Pi^5 \ tilde Pi^4` is the first source-faithful geometric shell in
which boundary-condition changes can occur.

This file records that shell literally.  It proves exact set decompositions
and volume-independent cardinality bounds only; it makes no claim that a
hard-support covariance difference is the printed `C_{Pi_0} - C_Pi`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal one-large-block shell surrounding `tilde Pi^4`. -/
noncomputable def cmp99SourcePi4Pi5LargeBlockShell {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) : Finset (FinBox 4 (2 * Q)) :=
  cmp99SourceTildePiLargeBlocks cell 5 \
    cmp99SourceTildePiLargeBlocks cell 4

/-- The inner cube lies in its printed one-block envelope. -/
theorem cmp99SourceTildePi4LargeBlocks_subset_pi5 {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    cmp99SourceTildePiLargeBlocks cell 4 ⊆
      cmp99SourceTildePiLargeBlocks cell 5 :=
  cmp99SourceTildePiLargeBlocks_mono cell (by omega)

/-- The envelope used at p. 408 lies in the larger boundary-condition cube
`tilde Pi^8` that appears at p. 415. -/
theorem cmp99SourceTildePi5LargeBlocks_subset_pi8 {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    cmp99SourceTildePiLargeBlocks cell 5 ⊆
      cmp99SourceTildePiLargeBlocks cell 8 :=
  cmp99SourceTildePiLargeBlocks_mono cell (by omega)

@[simp] theorem mem_cmp99SourcePi4Pi5LargeBlockShell_iff
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q)
    (block : FinBox 4 (2 * Q)) :
    block ∈ cmp99SourcePi4Pi5LargeBlockShell cell ↔
      block ∈ cmp99SourceTildePiLargeBlocks cell 5 ∧
        block ∉ cmp99SourceTildePiLargeBlocks cell 4 := by
  simp [cmp99SourcePi4Pi5LargeBlockShell]

/-- Exact decomposition of the printed envelope into the inner cube and its
one-large-block shell. -/
theorem cmp99SourceTildePi4_union_shell_eq_pi5 {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    cmp99SourceTildePiLargeBlocks cell 4 ∪
        cmp99SourcePi4Pi5LargeBlockShell cell =
      cmp99SourceTildePiLargeBlocks cell 5 := by
  classical
  ext block
  simp only [Finset.mem_union,
    mem_cmp99SourcePi4Pi5LargeBlockShell_iff]
  constructor
  · rintro (hinner | ⟨houter, _⟩)
    · exact cmp99SourceTildePi4LargeBlocks_subset_pi5 cell hinner
    · exact houter
  · intro houter
    by_cases hinner : block ∈ cmp99SourceTildePiLargeBlocks cell 4
    · exact Or.inl hinner
    · exact Or.inr ⟨houter, hinner⟩

/-- The inner cube and its shell are disjoint by construction. -/
theorem disjoint_cmp99SourceTildePi4LargeBlocks_shell
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) :
    Disjoint (cmp99SourceTildePiLargeBlocks cell 4)
      (cmp99SourcePi4Pi5LargeBlockShell cell) := by
  classical
  rw [Finset.disjoint_left]
  intro block hinner hshell
  exact (mem_cmp99SourcePi4Pi5LargeBlockShell_iff cell block).mp hshell |>.2 hinner

/-- Uniform shell bound inherited from the exact side-twelve envelope. -/
theorem card_cmp99SourcePi4Pi5LargeBlockShell_le {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    (cmp99SourcePi4Pi5LargeBlockShell cell).card ≤ 20736 := by
  exact (Finset.card_le_card Finset.sdiff_subset).trans
    (card_cmp99SourceTildePi5LargeBlocks_le cell)

/-- When side twelve embeds without wraparound, the shell has exactly the
difference of the two printed cube volumes. -/
theorem card_cmp99SourcePi4Pi5LargeBlockShell_eq {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (hfit : 12 ≤ 2 * Q) :
    (cmp99SourcePi4Pi5LargeBlockShell cell).card = 10736 := by
  have h4fit : 10 ≤ 2 * Q := by omega
  have hsub := cmp99SourceTildePi4LargeBlocks_subset_pi5 cell
  have hcard5 := card_cmp99SourceTildePiLargeBlocks_eq cell 5 (by simpa using hfit)
  have hcard4 := card_cmp99SourceTildePiLargeBlocks_eq cell 4 (by simpa using h4fit)
  rw [cmp99SourcePi4Pi5LargeBlockShell, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hsub, hcard5, hcard4]
  norm_num

end

end YangMills.RG
