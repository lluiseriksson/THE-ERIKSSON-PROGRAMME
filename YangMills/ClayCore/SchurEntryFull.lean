/-
  YangMills/ClayCore/SchurEntryFull.lean

  Milestone L2.6 step 2: full matrix-entry Schur orthogonality on SU(N).

      ∫_{SU(N)} U_{ij} · star(U_{kl}) dHaar = (1 / N) · δ_{ik} · δ_{jl}

  Packaging theorem. Combines:
    * L2.6 step 1b (SchurEntryOffDiag.lean):
        sunHaarProb_entry_offdiag_general — off-diagonals (i ≠ k ∨ j ≠ l) vanish
    * L2.6 step 1c (SchurEntryDiagonal.lean):
        sunHaarProb_entry_normSq_eq_inv_N — diagonal (i,j) = (k,l) gives 1/N

  Proof: one `by_cases` on `i = k ∧ j = l`, then a direct apply in each branch.

  Status: no sorry, no new axioms.
  Oracle must remain [propext, Classical.choice, Quot.sound].

  NOTE on file name: the README §5.2 refers to this target as
  `SchurEntryOrthogonality.lean`, but that filename is currently occupied by
  the phase-setup file (defines antiSymAngle / piAntiSymSU). Landing step 2
  in `SchurEntryFull.lean` avoids an import-graph refactor; a later commit
  may rename the two files to match the README naming.
-/

import YangMills.ClayCore.SchurEntryDiagonal
import YangMills.ClayCore.SchurEntryOffDiag

noncomputable section

open MeasureTheory Matrix Complex

namespace YangMills.ClayCore

variable {N : ℕ} [NeZero N]

/-- **L2.6 step 2 — Full matrix-entry Schur orthogonality on SU(N).**

For any indices `i, k, j, l : Fin N` of a Haar-distributed
`U ∈ Matrix.specialUnitaryGroup (Fin N) ℂ`,

    ∫ U_{ij} · star(U_{kl}) dHaar = (1/N) · δ_{ik} · δ_{jl}

written in Lean as a conditional expression: `1/N` on the diagonal
`(i,j) = (k,l)` and `0` otherwise. This packages the four-case analysis of
matrix-entry Schur orthogonality in a single statement. Combines
`sunHaarProb_entry_normSq_eq_inv_N` (step 1c, diagonal `= 1/N`) with
`sunHaarProb_entry_offdiag_general` (step 1b, off-diagonal `= 0`). -/
theorem sunHaarProb_entry_orthogonality (i k j l : Fin N) :
    (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N))
      = if i = k ∧ j = l then (1 : ℂ) / (N : ℂ) else 0 := by
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩]
    exact sunHaarProb_entry_normSq_eq_inv_N i j
  · rw [if_neg h]
    exact sunHaarProb_entry_offdiag_general i k j l (not_and_or.mp h)

end YangMills.ClayCore

end
