import YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusScalar
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius
import YangMills.RG.BalabanCMP99ComplexUbarSmallFieldPropagation

/-!
It identifies the proof-free closed scalar recursion with the literal
Eq. (3.37) four-Wilson-line radius and with the canonical no-winding record.
No per-scale gate, radius family or free deviation estimate is introduced.
-/

namespace YangMills.RG

noncomputable section

/-- The proof-free deviation radius is definitionally the common four-path
Eq. (3.37) envelope after fixing the printed path length. -/
theorem cmp99ComplexClosedRadiusDeviation_eq_eq337Uniform
    (d M : ℕ) (r : ℝ) :
    cmp99ComplexClosedRadiusDeviation (d * (M - 1)) r =
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r := by
  simp only [cmp99ComplexClosedRadiusDeviation,
    cmp99ComplexClosedRadiusFactorEnvelope,
    cmp99Eq337SourceComplexUbarUniformDeviationRadius,
    cmp99ComplexFourWilsonUniformDeviationBudget,
    cmp99ComplexFourFactorDeviationBudget]
  ring

/-- The proof-free logarithmic radius is the literal logarithmic radius of
the canonical no-winding budget carrying the same deviation. -/
theorem cmp99ComplexClosedRadiusLog_eq_ubarLogRadius
    {Nc : ℕ} [NeZero Nc] (delta : ℝ)
    (hnoWinding : delta < cmp99UbarNoWindingThreshold Nc) :
    cmp99ComplexClosedRadiusLog delta =
      cmp99UbarLogRadius
        (cmp99PhysicalNoWindingBudget (Nc := Nc) delta hnoWinding) := by
  rfl

/-- The proof-free exponential radius is the literal exponential radius of
the same canonical no-winding budget. -/
theorem cmp99ComplexClosedRadiusExp_eq_ubarExpRadius
    {Nc : ℕ} [NeZero Nc] (delta : ℝ)
    (hnoWinding : delta < cmp99UbarNoWindingThreshold Nc) :
    cmp99ComplexClosedRadiusExp delta =
      cmp99UbarExpRadius
        (cmp99PhysicalNoWindingBudget (Nc := Nc) delta hnoWinding) := by
  rfl

/-- After fixing the printed four-path length, the proof-free positive-edge
radius is exactly the radius of the literal complex Ubar source step. -/
theorem cmp99ComplexClosedRadiusNextLink_eq_sourceNextLinkRadius
    {Nc : ℕ} [NeZero Nc] (d M : ℕ) (r : ℝ)
    (hnoWinding :
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r <
        cmp99UbarNoWindingThreshold Nc) :
    cmp99ComplexClosedRadiusNextLink (d * (M - 1)) M r =
      cmp99SourceComplexUbarNextLinkRadius (Nc := Nc) M r
        (cmp99SourceComplexUbarNoWindingBudget
          d M Nc r hnoWinding) := by
  simp [cmp99ComplexClosedRadiusNextLink,
    cmp99SourceComplexUbarNextLinkRadius,
    cmp99ComplexClosedRadiusExp,
    cmp99ComplexClosedRadiusLog,
    cmp99UbarExpRadius,
    cmp99UbarLogRadius,
    cmp99SourceComplexUbarNoWindingBudget_delta,
    cmp99ComplexClosedRadiusDeviation_eq_eq337Uniform]

/-- The proof-free all-orientation recursion is exactly the literal source
radius after paying the same non-unitary inverse loss. -/
theorem cmp99ComplexClosedRadiusNext_eq_sourceNextOrientedLinkRadius
    {Nc : ℕ} [NeZero Nc] (d M : ℕ) (r : ℝ)
    (hnoWinding :
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r <
        cmp99UbarNoWindingThreshold Nc) :
    cmp99ComplexClosedRadiusNext (d * (M - 1)) M r =
      cmp99SourceComplexUbarNextOrientedLinkRadius (Nc := Nc) M r
        (cmp99SourceComplexUbarNoWindingBudget
          d M Nc r hnoWinding) := by
  unfold cmp99ComplexClosedRadiusNext
    cmp99SourceComplexUbarNextOrientedLinkRadius
  rw [cmp99ComplexClosedRadiusNextLink_eq_sourceNextLinkRadius
    (Nc := Nc) d M r hnoWinding]

/-- The single closed scalar budget constructs the literal no-winding record
at every nonterminal scale.  No per-scale radius family or gate is accepted. -/
noncomputable def cmp99ComplexClosedRadiusPhysicalNoWindingBudget
    (d M Nc depth : ℕ) [NeZero Nc] [NeZero M]
    [NeZero (d * (M - 1))]
    (r0 R : ℝ)
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth r0 R (cmp99UbarNoWindingThreshold Nc))
    (k : ℕ) (hk : k < depth) :
    MatrixNearLogNoWindingBudget Nc :=
  cmp99SourceComplexUbarNoWindingBudget d M Nc
    (cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 k) (by
      rw [← cmp99ComplexClosedRadiusDeviation_eq_eq337Uniform]
      exact B.deviation_lt_threshold hk)

/-- At every nonterminal scale, the proof-free successor is the literal
physical complex Ubar successor built from the one closed scalar budget. -/
theorem cmp99ComplexClosedRadiusAt_succ_eq_sourceNextOrientedLinkRadius
    (d M Nc depth : ℕ) [NeZero Nc] [NeZero M]
    [NeZero (d * (M - 1))]
    (r0 R : ℝ)
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth r0 R (cmp99UbarNoWindingThreshold Nc))
    (k : ℕ) (hk : k < depth) :
    cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 (k + 1) =
      cmp99SourceComplexUbarNextOrientedLinkRadius (Nc := Nc) M
        (cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 k)
        (cmp99ComplexClosedRadiusPhysicalNoWindingBudget
          d M Nc depth r0 R B k hk) := by
  rw [cmp99ComplexClosedRadiusAt_succ]
  unfold cmp99ComplexClosedRadiusPhysicalNoWindingBudget
  apply cmp99ComplexClosedRadiusNext_eq_sourceNextOrientedLinkRadius

end

end YangMills.RG
