import YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice

/-!
# The zero-parameter baseline in the CMP99 (3.59)--(3.60) real slice

The analytic perturbation constructor at parameter zero is exactly the
canonical complex embedding of the physical background.  The perturbing
one-cochain is physical and is complexified internally; no second background
or finished equality is supplied by the caller.
-/

namespace YangMills.RG

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The baseline analytic background is independent of the physical
one-cochain at zero parameter.  This is a named composition of the sealed
real-slice theorem and the sealed zero-variation identity. -/
theorem cmp99Eq337PhysicalComplexPerturbedBackground_zero_realSlice
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    cmp99Eq337PhysicalComplexPerturbedBackground U
        (cmp99Eq337PhysicalComplexifyOneCochain A) 0 =
      cmp99PhysicalGaugeBackgroundToSpecialLinear U := by
  simpa using
    (cmp99Eq337PhysicalComplexPerturbedBackground_realSlice U A 0)

end

end YangMills.RG
