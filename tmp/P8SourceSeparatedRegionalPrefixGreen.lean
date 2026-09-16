import tmp.P7SourceSeparatedAmbientPrefixPrecision
import YangMills.RG.BalabanCMP99SourceGeneratedRegionalFinePartition
import YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

# Exact source-separated local Green for CMP96 (2.40)--(2.43)

The Dirichlet region is the finite-range thickening of one literal separated
large-block cutoff.  Its ambient side is `K * L^(depth+1)`, while the precision
range is `L^(depth+1)`; `K` is never identified with `L`.  The local precision
is the compression of P7's exact CMP85 prefix precision, and its Green is the
canonical inverse generated from the transported coercivity theorem.

No region, Green, inverse law, coercivity witness or action estimate is a
caller input.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroScratchSourceSeparatedLargeBlockSide
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth) :=
  ⟨Nat.mul_pos (NeZero.pos K)
    (pow_pos (NeZero.pos L) (depth + 1)) |>.ne'⟩

/-- Canonical local region: exact nonzero cutoff support thickened by the
literal range `L^(depth+1)` of the source prefix precision. -/
noncomputable def scratch_cmp96SourceSeparatedRegionalCell
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (cell : FinBox 4 Q) :
    ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  cmp99RegionalFineSupportThickening
    (cmp99SourceSeparatedLargeBlockSquarePartition
      (L := L) (K := K) (Q := Q) (depth := depth) P)
    (L ^ (depth + 1)) cell

/-- The local region has the exact collar required by the finite range of the
source prefix precision. -/
theorem scratch_cmp96SourceSeparatedRegionalCell_hasFiniteRangeMargin
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    CMP99RegionalSquarePartitionHasFiniteRangeMargin
      (cmp99SourceSeparatedLargeBlockSquarePartition
        (L := L) (K := K) (Q := Q) (depth := depth) P)
      (scratch_cmp96SourceSeparatedRegionalCell P L K Q depth)
      (L ^ (depth + 1)) :=
  cmp99RegionalFineSupportThickening_hasFiniteRangeMargin
    (cmp99SourceSeparatedLargeBlockSquarePartition
      (L := L) (K := K) (Q := Q) (depth := depth) P)
    (L ^ (depth + 1))

/-- Dirichlet compression of the one exact P7 ambient precision. -/
noncomputable def scratch_cmp96SourceSeparatedRegionalPrefixPrecision
    (P : CMP95SourceSmoothPartitionProfile)
    (hL : 2 ≤ L) (depth : ℕ) (spacing epsilon a : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q) :
    ActiveGaugeZeroCochain
        (scratch_cmp96SourceSeparatedRegionalCell P L K Q depth cell)
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (scratch_cmp96SourceSeparatedRegionalCell P L K Q depth cell)
        (SUNLieCoord Nc) :=
  cmp99RegionalDirichletPrecision
    (scratch_cmp96SourceSeparatedRegionalCell P L K Q depth cell)
    (scratch_cmp89SourceSeparatedAmbientPrefixPrecision hL depth
      spacing epsilon a background budget fineSmall)

/-- Canonical local Green generated from that exact regional compression and
the transported P7 coercivity constant. -/
noncomputable def scratch_cmp96SourceSeparatedRegionalPrefixGreen
    (P : CMP95SourceSmoothPartitionProfile)
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    ActiveGaugeZeroCochain
        (scratch_cmp96SourceSeparatedRegionalCell P L K Q depth cell)
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (scratch_cmp96SourceSeparatedRegionalCell P L K Q depth cell)
        (SUNLieCoord Nc) :=
  cmp99RegionalDirichletGreen
    (scratch_cmp96SourceSeparatedRegionalCell P L K Q depth cell)
    (scratch_cmp89SourceSeparatedAmbientPrefixPrecision hL depth
      spacing epsilon a background budget fineSmall)
    (scratch_cmp89SourceSeparatedPrefixCoercivity_pos hL depth
      hspacing ha background budget fineSmall hsmall)
    (scratch_isCoerciveCLM_cmp89SourceSeparatedAmbientPrefixPrecision
      hL depth hspacing ha background budget fineSmall hsmall)

/-- The exact local precision followed by its internally generated Green is
the identity. -/
theorem scratch_cmp96SourceSeparatedRegionalPrefixPrecision_comp_green
    (P : CMP95SourceSmoothPartitionProfile)
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    (scratch_cmp96SourceSeparatedRegionalPrefixPrecision P hL depth
      spacing epsilon a background budget fineSmall cell).comp
        (scratch_cmp96SourceSeparatedRegionalPrefixGreen P hL depth
          hspacing ha background budget fineSmall hsmall cell) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain
          (scratch_cmp96SourceSeparatedRegionalCell P L K Q depth cell)
          (SUNLieCoord Nc)) := by
  apply cmp99RegionalDirichletPrecision_comp_green

end

end YangMills.RG
