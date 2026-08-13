/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99OneScaleRegionalPoincare
import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeMassComplexFieldDictionary

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

# Global zero-extension dictionary for the generated complex field

The explicit finite sum of transported full-box coordinate deltas is exactly
the pointwise complexification of Dirichlet extension by zero.  The statement
is global on the generated fine box: membership gives the unique active delta,
while non-membership kills every delta.

Only the canonical finite-box equivalence is used, through its injectivity.
No equality between the generated active carrier and the periodic full box is
asserted, and no Laplacian, precision, inverse or Green operator is identified.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The explicit transported complex field is the complexification of the
literal Dirichlet zero extension at every generated full-box site. -/
theorem cmp99SourceGeneratedTerminalComplexZeroExtension_apply_eq_complexification_extendZero
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (eta : PiLp 2 (fun _ : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
        SUNLieCoord Nc))
    (x : FinBox d (cmp99RegionalLatticeSize M N (depth + 1))) :
    cmp99SourceGeneratedTerminalComplexZeroExtension
        (M := M) (Nc := Nc) Omega depth eta
          (cmp99GeneratedFineBoxOneBlockEquiv
            (d := d) M N (depth + 1) x) =
      cmp99SUNLieCoordComplexificationLM Nc
        (extendZeroZeroCLM
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) eta x) := by
  classical
  let region := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let e := cmp99GeneratedFineBoxOneBlockEquiv (d := d) M N (depth + 1)
  by_cases hx : x ∈ region.sites
  · let source : ActiveGaugeRegion.Site region := ⟨x, hx⟩
    rw [extendZeroZeroCLM_apply_of_mem region eta x hx]
    unfold cmp99SourceGeneratedTerminalComplexZeroExtension
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single source]
    · simp [source, cmp99SourceFlatFullComplexSingle]
    · intro other _hother hne
      have htarget : e x ≠ e other.1 := by
        intro heq
        apply hne
        apply Subtype.ext
        exact e.injective heq.symm
      simp only [cmp99SourceFlatFullComplexSingle]
      rw [if_neg htarget]
    · intro hnot
      exact (hnot (Finset.mem_univ source)).elim
  · rw [extendZeroZeroCLM_apply_of_not_mem region eta x hx, map_zero]
    unfold cmp99SourceGeneratedTerminalComplexZeroExtension
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro source _hsource
    have htarget : e x ≠ e source.1 := by
      intro heq
      apply hx
      have hval : x = source.1 := e.injective heq
      simpa [region, hval] using source.2
    simp only [cmp99SourceFlatFullComplexSingle]
    rw [if_neg htarget]

end

end YangMills.RG
