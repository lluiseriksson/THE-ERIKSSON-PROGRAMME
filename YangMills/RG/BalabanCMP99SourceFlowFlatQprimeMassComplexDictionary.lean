/-
PRE-VALIDATION -- source present; `.olean` not yet materialized and the
result is not yet compiler-verified.
-/

import YangMills.RG.BalabanCMP99SourceFlowFlatPrecisionScalarDictionary
import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeMassComplexFieldDictionary

/-!
# Complex dictionary for the literal source-flow flat `Q'^*Q'` mass

The geometric one-block kernel is independent of the scalar mass convention.
This file first exposes that fact with one explicit scalar equality, then
specializes it to the literal source-flow coefficients using the sealed
`R^d * R^-2d = R^-d` dictionary.  Finally it sums coordinate deltas to obtain
the field statement.

The source specialization constructs its scalar equality internally.  It
does not identify Laplacians or full precisions, construct an inverse, or
assert a regional Green estimate.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Coordinate kernel dictionary for any two real coefficients whose
complex casts obey the exact weighted/counting normalization. -/
theorem cmp99SourceCountingMass_complexCoordinateDictionary_of_scalar
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (countingA weightedA : ℝ)
    (hscalar :
      ((weightedA : ℝ) : ℂ) *
          ((cmp99SourceBlockAverageWeight (M ^ (depth + 1)) d : ℝ) : ℂ) =
        ((countingA : ℝ) : ℂ) *
          ((cmp99SourceBlockAverageWeight
            (M ^ (depth + 1)) d : ℝ) : ℂ) ^ 2)
    (source target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
    (v : SUNLieCoord Nc) :
    let regions :=
      cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)
    let sourceBox := cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N (depth + 1) source.1
    let targetBox := cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N (depth + 1) target.1
    cmp99SUNLieCoordComplexificationLM Nc
        (countingA •
          (((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
            (regions.flatExplicitQprime (Nc := Nc)))
              (singleFinitePiLp source v) target)) =
      ((weightedA : ℝ) : ℂ) •
        cmp99SourceFlatFullComplexQprimeMass
          (M := M ^ (depth + 1)) (N' := N)
          (cmp99SourceFlatFullComplexSingle sourceBox
            (cmp99SUNLieCoordComplexificationLM Nc v)) targetBox := by
  classical
  dsimp only
  rw [cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply_oneBlock]
  rw [cmp99SourceFlatFullComplexQprimeMass_single_apply]
  by_cases howner :
      blockSite (M ^ (depth + 1)) N
          (cmp99GeneratedFineBoxOneBlockEquiv
            (d := d) M N (depth + 1) target.1) =
        blockSite (M ^ (depth + 1)) N
          (cmp99GeneratedFineBoxOneBlockEquiv
            (d := d) M N (depth + 1) source.1)
  · rw [if_pos howner, if_pos howner]
    ext a
    simp only [cmp99SUNLieCoordComplexificationLM_apply,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
    push_cast
    let va : ℂ := ((v.ofLp a : ℝ) : ℂ)
    let w : ℂ :=
      ((cmp99SourceBlockAverageWeight (M ^ (depth + 1)) d : ℝ) : ℂ)
    let mass : ℂ := ((countingA : ℝ) : ℂ)
    let A : ℂ := ((weightedA : ℝ) : ℂ)
    change mass * (w ^ 2 * va) = A * (w * va)
    calc
      mass * (w ^ 2 * va) = (mass * w ^ 2) * va := (mul_assoc _ _ _).symm
      _ = (A * w) * va := congrArg (fun z : ℂ => z * va) hscalar.symm
      _ = A * (w * va) := mul_assoc _ _ _
  · rw [if_neg howner, if_neg howner]
    simp

/-- Literal source-flow specialization.  The scalar compatibility premise
is discharged by the source-flow normalization theorem. -/
theorem cmp99SourceFlowCountingMass_complexCoordinateDictionary
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) (a : ℝ)
    (source target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
    (v : SUNLieCoord Nc) :
    let regions :=
      cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)
    let sourceBox := cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N (depth + 1) source.1
    let targetBox := cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N (depth + 1) target.1
    cmp99SUNLieCoordComplexificationLM Nc
        (cmp99SourceFlowFlatCountingA d a M depth •
          (((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
            (regions.flatExplicitQprime (Nc := Nc)))
              (singleFinitePiLp source v) target)) =
      ((cmp99SourceFlowFlatFullComplexA a M depth : ℝ) : ℂ) •
        cmp99SourceFlatFullComplexQprimeMass
          (M := M ^ (depth + 1)) (N' := N)
          (cmp99SourceFlatFullComplexSingle sourceBox
            (cmp99SUNLieCoordComplexificationLM Nc v)) targetBox := by
  exact cmp99SourceCountingMass_complexCoordinateDictionary_of_scalar
    Omega depth
    (cmp99SourceFlowFlatCountingA d a M depth)
    (cmp99SourceFlowFlatFullComplexA a M depth)
    (cmp99SourceFlowFlatFullComplexA_mul_weight_complex d M depth a)
    source target v

/-- The source-flow counting mass on an arbitrary real active field agrees,
after pointwise complexification, with the literal full-box weighted mass of
its explicit zero extension at every transported active target. -/
theorem cmp99SourceFlowCountingMass_complexFieldDictionary
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) (a : ℝ)
    (eta : PiLp 2 (fun _ : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
        SUNLieCoord Nc))
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) :
    let regions :=
      cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)
    let targetBox := cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N (depth + 1) target.1
    cmp99SUNLieCoordComplexificationLM Nc
        (cmp99SourceFlowFlatCountingA d a M depth •
          (((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
            (regions.flatExplicitQprime (Nc := Nc))) eta target)) =
      ((cmp99SourceFlowFlatFullComplexA a M depth : ℝ) : ℂ) •
        cmp99SourceFlatFullComplexQprimeMass
          (M := M ^ (depth + 1)) (N' := N)
          (cmp99SourceGeneratedTerminalComplexZeroExtension
            (M := M) (Nc := Nc) Omega depth eta) targetBox := by
  classical
  dsimp only
  have heta : eta = ∑ source, singleFinitePiLp source (eta source) :=
    (sum_singleFinitePiLp_eq eta).symm
  conv_lhs =>
    rw [heta]
  rw [map_sum]
  rw [finitePiLp_sum_apply]
  rw [Finset.smul_sum]
  rw [map_sum]
  unfold cmp99SourceGeneratedTerminalComplexZeroExtension
  rw [cmp99SourceFlatFullComplexQprimeMass_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro source _hsource
  exact cmp99SourceFlowCountingMass_complexCoordinateDictionary
    Omega depth a source target (eta source)

end

end YangMills.RG
