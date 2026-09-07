import YangMills.RG.BalabanCMP89CanonicalNeumannReflectionRepresentation
import YangMills.RG.BalabanCMP89NeumannScalarReflectionOperator
import YangMills.RG.BalabanCMP99SourcePi4WeakenedCoarseMiddle

/-!
# Compiler-verified conditional CMP89 (2.42) producer by inverse uniqueness

Cold-sealed at source checkpoint `cdd859ba99671e83a1ef2b3d8119a4e376a97ced`;
see Verification Ledger Addendum 1003.

This module does not accept the printed reflection equality. Instead it
constructs the finite reflection-series operator internally and asks for the
physical statement that this operator is a right inverse of the same regional
precision. Coercivity then identifies it with the canonical regional Green,
yielding the exact source certificate.
-/

namespace YangMills.RG

noncomputable section

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {Omega : ActiveGaugeRegion d N} {g : Type*}
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]

/-- Inverse-uniqueness producer for the canonical CMP89 multiple-reflection
gate. The only analytic equality accepted is the right-inverse law of the
internally constructed image operator; the target representation equality is
derived. -/
theorem cmp89CanonicalNeumannReflectionRepresentation_of_rightInverse
    {m : Fin d → ℤ}
    (siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃
      ActiveGaugeRegion.Site Omega)
    (precision green : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    {c : ℝ} (hc : 0 < c) (hcoercive : IsCoerciveCLM precision c)
    (hgreen : precision.comp green =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain Omega g))
    (himage : precision.comp
        (cmp89NeumannScalarReflectionOperator
          (g := g) siteEquiv fullGreen) =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain Omega g))
    (hside : ∀ mu, 0 < m mu)
    (hsummable : ∀ x n : CMP89SourceNeumannIntegerRectanglePoint m,
      Summable (fun k : Fin d → ℤ =>
        ∑ branch : CMP89NeumannReflectionBranch d,
          fullGreen x.1
            (cmp89NeumannReflectionImage m n.1 k branch))) :
    CMP89CanonicalNeumannReflectionRepresentation
      (d := d) (N := N) (Omega := Omega) siteEquiv green
        (fun x y v => fullGreen x y • v) := by
  let imageGreen :=
    cmp89NeumannScalarReflectionOperator (g := g) siteEquiv fullGreen
  have heq : imageGreen = green :=
    rightInverse_unique_of_isCoerciveCLM
      precision imageGreen green hc hcoercive himage hgreen
  intro v
  refine
    { side_pos := hside
      summable := ?_
      representation := ?_ }
  · intro x n
    have hs := hsummable x n
    have hterm : (fun k : Fin d → ℤ =>
        ∑ branch : CMP89NeumannReflectionBranch d,
          fullGreen x.1
              (cmp89NeumannReflectionImage m n.1 k branch) • v) =
        (fun k : Fin d → ℤ =>
          (∑ branch : CMP89NeumannReflectionBranch d,
            fullGreen x.1
              (cmp89NeumannReflectionImage m n.1 k branch)) • v) := by
      funext k
      rw [Finset.sum_smul]
    rw [hterm]
    exact hs.smul_const v
  · intro x n
    have hentry :
        imageGreen (singleFinitePiLp (siteEquiv n) v) (siteEquiv x) =
          green (singleFinitePiLp (siteEquiv n) v) (siteEquiv x) := by
      have happ := congrArg
        (fun T : ActiveGaugeZeroCochain Omega g →L[ℝ]
            ActiveGaugeZeroCochain Omega g =>
          T (singleFinitePiLp (siteEquiv n) v) (siteEquiv x)) heq
      exact happ
    calc
      cmp89FinitePiLpGreenEntryAt green (siteEquiv x) (siteEquiv n) v =
          imageGreen (singleFinitePiLp (siteEquiv n) v) (siteEquiv x) := by
        exact hentry.symm
      _ = cmp89NeumannReflectionSeries fullGreen m x.1 n.1 • v := by
        exact cmp89NeumannScalarReflectionOperator_single
          siteEquiv fullGreen x n v
      _ = cmp89NeumannReflectionSeries
          (fun y z => fullGreen y z • v) m x.1 n.1 := by
        exact (cmp89NeumannReflectionSeries_smul
          (hsummable x n) v).symm

end

end YangMills.RG
