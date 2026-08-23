import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreen
import YangMills.RG.BalabanCMP99SourceFlatGeneratedPrecisionScalarDictionary

/-!
# Scalar dictionary for the literal source-flow flat precision

At generated depth `depth + 1`, canonical fine spacing makes the terminal
spacing exactly one.  Hence the printed weighted coefficient is the literal
source value `a_depth`, whereas Lean's counting-Hilbert coefficient is
`a_depth * R^d`, with `R = L^(depth+1)`.  Multiplication by the two counting
average weights cancels one factor `R^d` and leaves the single weighted
average coefficient used by the full-complex source precision.

All normalization factors remain visible.  This file proves only scalar
identities; it does not identify carriers, Laplacians, precisions, inverses or
regional Green operators.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N] [NeZero Nc]
variable {rho : SUNAdjointModel Nc}
variable {Omega : ActiveGaugeRegion d N}
variable {background : GaugeConfig d N (SUN Nc)}

/-- Literal source coefficient paired with the coefficient-one weighted
adjoint at generated depth `depth + 1`. -/
noncomputable def cmp99SourceFlowFlatFullComplexA
    (a : ℝ) (L depth : ℕ) : ℝ :=
  cmp99SourceMassParameter a (L : ℝ) depth

/-- The same source mass in Lean's counting-Hilbert convention. -/
noncomputable def cmp99SourceFlowFlatCountingA
    (d : ℕ) (a : ℝ) (L depth : ℕ) : ℝ :=
  cmp99SourceFlowFlatFullComplexA a L depth *
    (((cmp99SourceGeneratedFullComplexBlockSide L (depth + 1) : ℕ) : ℝ) ^ d)

/-- Canonical fine spacing makes the final retained source prefix a
unit-spacing object. -/
theorem cmp85LastPositivePrefix_sourceFlow_terminalSpacing_eq_one
    (depth : ℕ)
    (T : CMP99SourceRetainedPhysicalTower rho Omega L
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1))
      background (depth + 1)) :
    (T.towerAt
      (cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth)).1).terminalSpacing =
      1 := by
  have hL0 : (L : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hpow : (L : ℝ) ^ (depth + 1) ≠ 0 :=
    pow_ne_zero _ hL0
  rw [T.towerAt_terminalSpacing]
  simp [cmp85LastPositivePrefix,
    cmp99SourceGeneratedFullComplexSpacing,
    cmp99SourceGeneratedFullComplexBlockSide, Nat.cast_pow,
    hpow]

/-- The final printed weighted coefficient is exactly the literal source
flow `a_depth`; no generated Poincare coefficient occurs. -/
theorem cmp85LastPositivePrefix_sourceFlow_weightedCoefficient_eq
    (depth : ℕ) (a : ℝ)
    (T : CMP99SourceRetainedPhysicalTower rho Omega L
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1))
      background (depth + 1)) :
    cmp85SourcePrefixWeightedCoefficient T a
        (cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth)) =
      cmp99SourceFlowFlatFullComplexA a L depth := by
  unfold cmp85SourcePrefixWeightedCoefficient
  rw [cmp85LastPositivePrefix_succ_sourceA_eq_massParameter]
  rw [cmp85LastPositivePrefix_sourceFlow_terminalSpacing_eq_one
    (depth := depth) T]
  simp [cmp99SourceFlowFlatFullComplexA]

/-- Exact counting-Hilbert coefficient at the final source prefix.  The
factor `R^d` is the terminal/fine volume ratio and is applied exactly once. -/
theorem cmp85LastPositivePrefix_sourceFlow_countingCoefficient_eq
    (depth : ℕ) (a : ℝ)
    (T : CMP99SourceRetainedPhysicalTower rho Omega L
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1))
      background (depth + 1)) :
    cmp85SourcePrefixCountingCoefficient T a
        (cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth)) =
      cmp99SourceFlowFlatCountingA d a L depth := by
  unfold cmp85SourcePrefixCountingCoefficient cmp85SourcePrefixVolumeRatio
  rw [cmp85LastPositivePrefix_sourceFlow_weightedCoefficient_eq depth a T]
  rw [cmp85LastPositivePrefix_sourceFlow_terminalSpacing_eq_one
    (depth := depth) T]
  simp [cmp99SourceFlowFlatCountingA,
    cmp99SourceGeneratedFullComplexSpacing,
    cmp99SourceGeneratedFullComplexBlockSide, Nat.cast_pow, ← inv_pow]

/-- The counting coefficient times two counting-average weights is exactly
the printed coefficient times the single weighted-average weight. -/
theorem cmp99SourceFlowFlatFullComplexA_mul_weight
    (d L depth : ℕ) [NeZero L] (a : ℝ) :
    cmp99SourceFlowFlatFullComplexA a L depth *
        cmp99SourceBlockAverageWeight
          (cmp99SourceGeneratedFullComplexBlockSide L (depth + 1)) d =
      cmp99SourceFlowFlatCountingA d a L depth *
        (cmp99SourceBlockAverageWeight
          (cmp99SourceGeneratedFullComplexBlockSide L (depth + 1)) d) ^ 2 := by
  let R := cmp99SourceGeneratedFullComplexBlockSide L (depth + 1)
  letI : NeZero R := ⟨by
    dsimp [R, cmp99SourceGeneratedFullComplexBlockSide]
    exact pow_ne_zero _ (NeZero.ne L)⟩
  let A := cmp99SourceFlowFlatFullComplexA a L depth
  let w := cmp99SourceBlockAverageWeight R d
  have hw : (R : ℝ) ^ d * w = 1 := by
    exact card_mul_cmp99SourceBlockAverageWeight (M := R) (d := d)
  change A * w = (A * (R : ℝ) ^ d) * w ^ 2
  symm
  calc
    (A * (R : ℝ) ^ d) * w ^ 2 = A * (((R : ℝ) ^ d * w) * w) := by ring
    _ = A * w := by rw [hw, one_mul]

/-- Complex-cast form consumed by the full-complex coordinate dictionary. -/
theorem cmp99SourceFlowFlatFullComplexA_mul_weight_complex
    (d L depth : ℕ) [NeZero L] (a : ℝ) :
    ((cmp99SourceFlowFlatFullComplexA a L depth : ℝ) : ℂ) *
        ((cmp99SourceBlockAverageWeight
          (cmp99SourceGeneratedFullComplexBlockSide L (depth + 1)) d : ℝ) : ℂ) =
      ((cmp99SourceFlowFlatCountingA d a L depth : ℝ) : ℂ) *
        ((cmp99SourceBlockAverageWeight
          (cmp99SourceGeneratedFullComplexBlockSide L (depth + 1)) d : ℝ) : ℂ) ^ 2 := by
  exact_mod_cast cmp99SourceFlowFlatFullComplexA_mul_weight d L depth a

end

end YangMills.RG
