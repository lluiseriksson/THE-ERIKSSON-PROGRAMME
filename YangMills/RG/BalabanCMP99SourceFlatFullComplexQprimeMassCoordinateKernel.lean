/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionModeAction

/-!
# Coordinate kernel of the full-box flat complex `Q'^*Q'`

The full-complex precision uses the source-normalized average `Q'`, whose
one-block coefficient is `R^-d`, followed by the coefficient-one weighted
adjoint.  On a coordinate delta, their composition therefore carries exactly
one copy of `R^-d`: it is nonzero precisely on the fine sites having the same
literal `blockSite R N` owner as the source.

This is the coordinate-kernel gate for the full-box averaging term.  It does
not use a fibre-cardinality argument and does not identify a generated
precision, Laplacian, inverse or regional Green operator.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d R N Nc : ℕ}
variable [NeZero d] [NeZero R] [NeZero N] [NeZero Nc]

/-- Ordinary full-box complex coordinate delta, with no `PiLp` wrapper. -/
def cmp99SourceFlatFullComplexSingle
    (source : FinBox d (R * N)) (v : SUNLieComplexCoord Nc) :
    FinBox d (R * N) → SUNLieComplexCoord Nc :=
  fun x => if x = source then v else 0

omit [NeZero d] [NeZero Nc] in
/-- The source-normalized full-box average of one coordinate delta has one
copy of the literal block weight and is supported on its unique owner. -/
theorem cmp99SourceFlatComplexBlockAverage_full_single_apply
    (source : FinBox d (R * N)) (v : SUNLieComplexCoord Nc)
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := R) (N' := N)
        (cmp99SourceFlatFullFineRegion d (R * N)))) :
    cmp99SourceFlatComplexBlockAverageCLM
        (cmp99SourceFlatFullFineRegion d (R * N))
        (cmp99SourceFlatFullActiveComplexField
          (cmp99SourceFlatFullComplexSingle source v)) y =
      if y.1 = blockSite R N source then
        cmp99SourceBlockAverageWeight R d • v
      else 0 := by
  classical
  rw [cmp99SourceFlatComplexBlockAverageCLM_apply]
  simp only [cmp99SourceFlatFullActiveComplexField_apply]
  by_cases howner : y.1 = blockSite R N source
  · rw [if_pos howner]
    have hsource : source ∈ blockOf R N y.1 :=
      (mem_blockOf R N y.1 source).2 howner.symm
    let sourceInBlock : {x : FinBox d (R * N) // x ∈ blockOf R N y.1} :=
      ⟨source, hsource⟩
    simp only [cmp99SourceFlatFullComplexSingle,
      cmp99ActiveFineSiteOfBlock_val]
    rw [Finset.sum_eq_single sourceInBlock]
    · simp [sourceInBlock]
    · intro other _hother hne
      have hval : other.1 ≠ source := by
        intro heq
        apply hne
        exact Subtype.ext heq
      rw [if_neg hval]
    · intro hnot
      exact (hnot (Finset.mem_univ sourceInBlock)).elim
  · rw [if_neg howner]
    have hsource_ne
        (x : {x : FinBox d (R * N) // x ∈ blockOf R N y.1}) :
        x.1 ≠ source := by
      intro hx
      apply howner
      have hxowner := (mem_blockOf R N y.1 x.1).1 x.2
      simpa [hx] using hxowner.symm
    simp [cmp99SourceFlatFullComplexSingle, hsource_ne]

omit [NeZero d] [NeZero Nc] in
/-- Exact coordinate kernel of the literal full-box complex `Q'^*Q'`.
The coefficient-one weighted adjoint introduces no second block weight. -/
theorem cmp99SourceFlatFullComplexQprimeMass_single_apply
    (source target : FinBox d (R * N)) (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexQprimeMass
        (cmp99SourceFlatFullComplexSingle source v) target =
      if blockSite R N target = blockSite R N source then
        cmp99SourceBlockAverageWeight R d • v
      else 0 := by
  rw [cmp99SourceFlatFullComplexQprimeMass,
    cmp99SourceFlatComplexBlockWeightedAdjointCLM_apply,
    cmp99SourceFlatComplexBlockAverage_full_single_apply]

end

end YangMills.RG
