/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceOmegaGeometry
import YangMills.RG.BalabanCMP99SourceGlobalStratification

/-!
# The literal terminal domain in the CMP99 local Omega sequence

Printed CMP99 p. 408 fixes the final member of the local sequence by the
equation

`Omega_{j+1}(Pi) = tilde Pi^3 ∩ B^{j+1}(Lambda_{j+1})`.

The global stratification already stores the lifted fine-carrier stratum
`B^{j+1}(Lambda_{j+1})`.  This file therefore constructs the intersection
literally and inserts it into the existing coarse large-block geometry.

This does **not** select the earlier domains `Omega_n(Pi)`, `n < j`.  CMP96
(2.1)--(2.4) specifies an admissible nested family and CMP99 prescribes its
successive physical gaps on scale-dependent lattices.  Those gaps are finer
than the single large-block lattice used by `CMP99SourceOmegaGeometry`; a
future dependent-scale producer must retain them rather than round them away.
The constructor below is consequently a non-vacuity and terminal-dictionary
constructor, not a claim that Phase A1 is complete.
-/

namespace YangMills.RG

noncomputable section

/-- The global stratum index `j+1` occurring in the terminal local domain. -/
def cmp99OmegaTerminalGlobalStratumIndex (j : ℕ) : Fin (j + 2) :=
  ⟨j + 1, by omega⟩

/-- Literal CMP99 p. 408 terminal region
`tilde Pi^3 ∩ B^{j+1}(Lambda_{j+1})` on the large-block carrier. -/
noncomputable def cmp99SourceOmegaTerminalRegion
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) (j : ℕ)
    (Global : CMP99SourceGlobalStratification
      (FinBox 4 (2 * Q)) (j + 2)) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp99SourceTildePiLargeBlocks cell 3 ∩
    Global.stratum (cmp99OmegaTerminalGlobalStratumIndex j)

@[simp] theorem mem_cmp99SourceOmegaTerminalRegion_iff
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) (j : ℕ)
    (Global : CMP99SourceGlobalStratification
      (FinBox 4 (2 * Q)) (j + 2))
    (block : FinBox 4 (2 * Q)) :
    block ∈ cmp99SourceOmegaTerminalRegion cell j Global ↔
      block ∈ cmp99SourceTildePiLargeBlocks cell 3 ∧
        block ∈ Global.stratum
          (cmp99OmegaTerminalGlobalStratumIndex j) := by
  simp [cmp99SourceOmegaTerminalRegion]

/-- The terminal region lies in `tilde Pi^3` by its source definition. -/
theorem cmp99SourceOmegaTerminalRegion_subset_pi3
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) (j : ℕ)
    (Global : CMP99SourceGlobalStratification
      (FinBox 4 (2 * Q)) (j + 2)) :
    cmp99SourceOmegaTerminalRegion cell j Global ⊆
      cmp99SourceTildePiLargeBlocks cell 3 :=
  Finset.inter_subset_left

/-- Hence the printed terminal region lies in `tilde Pi^4`. -/
theorem cmp99SourceOmegaTerminalRegion_subset_pi4
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) (j : ℕ)
    (Global : CMP99SourceGlobalStratification
      (FinBox 4 (2 * Q)) (j + 2)) :
    cmp99SourceOmegaTerminalRegion cell j Global ⊆
      cmp99SourceTildePiLargeBlocks cell 4 :=
  (cmp99SourceOmegaTerminalRegion_subset_pi3 cell j Global).trans
    (cmp99SourceTildePiLargeBlocks_mono cell (by omega))

/-- The terminal domain inherits the printed side-eight cardinality budget,
uniformly in the ambient periodic volume. -/
theorem card_cmp99SourceOmegaTerminalRegion_le
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) (j : ℕ)
    (Global : CMP99SourceGlobalStratification
      (FinBox 4 (2 * Q)) (j + 2)) :
    (cmp99SourceOmegaTerminalRegion cell j Global).card ≤ 4096 := by
  exact (Finset.card_le_card
    (cmp99SourceOmegaTerminalRegion_subset_pi3 cell j Global)).trans
    (by simpa using card_cmp99SourceTildePiLargeBlocks_le cell 3)

namespace CMP99SourceOmegaGeometry

/-- Coarse non-vacuity witness with a prescribed terminal region.

All earlier entries are `tilde Pi^4`, while the last entry is `terminal`.
This is the unique minimal constructor available on the current single
large-block carrier.  It deliberately makes no source-gap claim: the
scale-dependent gap geometry cannot be represented by this coarse type. -/
noncomputable def ofTerminal
    {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q} {j : ℕ}
    (terminal : Finset (FinBox 4 (2 * Q)))
    (terminal_subset_pi4 : terminal ⊆
      cmp99SourceTildePiLargeBlocks cell 4) :
    CMP99SourceOmegaGeometry cell j where
  regions r := if r = cmp99OmegaLastIndex j then terminal
    else cmp99SourceTildePiLargeBlocks cell 4
  nested := by
    intro r s hrs block hblock
    by_cases hs : s = cmp99OmegaLastIndex j
    · rw [if_pos hs] at hblock
      by_cases hr : r = cmp99OmegaLastIndex j
      · simpa [hr] using hblock
      · rw [if_neg hr]
        exact terminal_subset_pi4 hblock
    · rw [if_neg hs] at hblock
      have hr : r ≠ cmp99OmegaLastIndex j := by
        intro hr
        subst r
        have : s = cmp99OmegaLastIndex j := by
          apply Fin.ext
          change s.val = j + 1
          have hsle : j + 1 ≤ s.val := hrs
          omega
        exact hs this
      simpa [hr] using hblock
  omega_j_eq_pi4 := by
    rw [if_neg]
    intro h
    have := congrArg Fin.val h
    simp [cmp99OmegaPi4Index, cmp99OmegaLastIndex] at this
  omega_zero_subset_pi5 := by
    rw [if_neg]
    · exact cmp99SourceTildePi4LargeBlocks_subset_pi5 cell
    · intro h
      have := congrArg Fin.val h
      simp [cmp99OmegaZeroIndex, cmp99OmegaLastIndex] at this

/-- Source-specific non-vacuity witness whose terminal member is the literal
intersection with the lifted global stratum. -/
noncomputable def ofGlobalStratification
    {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q} {j : ℕ}
    (Global : CMP99SourceGlobalStratification
      (FinBox 4 (2 * Q)) (j + 2)) :
    CMP99SourceOmegaGeometry cell j :=
  ofTerminal (cmp99SourceOmegaTerminalRegion cell j Global)
    (cmp99SourceOmegaTerminalRegion_subset_pi4 cell j Global)

@[simp] theorem ofTerminal_last_region
    {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q} {j : ℕ}
    (terminal : Finset (FinBox 4 (2 * Q)))
    (hterminal : terminal ⊆ cmp99SourceTildePiLargeBlocks cell 4) :
    (ofTerminal terminal hterminal).regions (cmp99OmegaLastIndex j) =
      terminal := by
  simp [ofTerminal]

@[simp] theorem ofGlobalStratification_last_region
    {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q} {j : ℕ}
    (Global : CMP99SourceGlobalStratification
      (FinBox 4 (2 * Q)) (j + 2)) :
    (ofGlobalStratification (cell := cell) Global).regions
        (cmp99OmegaLastIndex j) =
      cmp99SourceOmegaTerminalRegion cell j Global := by
  simp [ofGlobalStratification]

/-- For the source-specific witness, the final transition shell is exactly
`tilde Pi^4 \ (tilde Pi^3 ∩ B^{j+1}(Lambda_{j+1}))`. -/
theorem ofGlobalStratification_terminalTransitionShell
    {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q} {j : ℕ}
    (Global : CMP99SourceGlobalStratification
      (FinBox 4 (2 * Q)) (j + 2)) :
    (ofGlobalStratification (cell := cell) Global).terminalTransitionShell =
      cmp99SourceTildePiLargeBlocks cell 4 \
        cmp99SourceOmegaTerminalRegion cell j Global := by
  unfold terminalTransitionShell
  rw [CMP99SourceOmegaGeometry.omega_j_eq_pi4,
    ofGlobalStratification_last_region]

end CMP99SourceOmegaGeometry

end

end YangMills.RG
