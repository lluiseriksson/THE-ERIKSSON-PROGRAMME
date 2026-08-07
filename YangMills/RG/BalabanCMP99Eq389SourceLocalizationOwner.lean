/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition
import YangMills.RG.FinitePiLpBlockLocalizedSup

/-!
# PRE-VALIDATION: source localization owners for CMP99 (3.89)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

CMP99 (3.89) measures decay between localization blocks of side
`L^(depth+1)` on a carrier with `2*(K*Q)` such blocks.  The regional
construction stores the same fine torus as `K*L^(depth+1)` times `2*Q`.
This module records the exact equality and uses one explicit cast before
applying `blockSite` at the source scale.

The resulting predicate is the exact source-facing target for the physical
three-species operator.  No localized Green estimate or defect bound is
proved here.
-/

namespace YangMills.RG

noncomputable section

variable {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]

private instance instNeZeroEq389SourceLocalizationAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- The separated regional presentation and the source localization-block
presentation are the same fine carrier. -/
theorem cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier
    (L K Q depth : ℕ) :
    cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q) =
      L ^ (depth + 1) * (2 * (K * Q)) := by
  unfold cmp99SourceSeparatedLargeBlockSide
  ring

/-- Explicit equivalence from the separated regional presentation to the
source localization-block presentation. -/
noncomputable def cmp99Eq389SourceLocalizationSiteEquiv
    (L K Q depth : ℕ) :
    FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) ≃
      FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) :=
  Equiv.cast (congrArg (FinBox 4)
    (cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier L K Q depth))

/-- Owner of one fine site in the source's localization-block convention. -/
noncomputable def cmp99Eq389SourceLocalizationOwner
    (L K Q depth : ℕ) [NeZero L]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    FinBox 4 (2 * (K * Q)) :=
  blockSite (L ^ (depth + 1)) (2 * (K * Q))
    (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth x)

/-- Distance between fine sites measured between their source localization
owners, with divisor `L^(depth+1)` rather than `K*L^(depth+1)`. -/
noncomputable def cmp99Eq389SourceLocalizationDist
    (L K Q depth : ℕ) [NeZero L]
    (target source : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) : ℕ :=
  finBoxDist
    (cmp99Eq389SourceLocalizationOwner L K Q depth target)
    (cmp99Eq389SourceLocalizationOwner L K Q depth source)

/-- Exact source-facing form of a localized-action bound for an operator on
the separated ambient carrier. -/
def CMP99Eq389SourceLocalizedActionBound
    {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g]
    (depth : ℕ)
    (C : FinitePiLpField
        (FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) g →L[ℝ]
      FinitePiLpField
        (FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) g)
    (A rate : ℝ) : Prop :=
  FinitePiLpTypedBlockLocalizedSupBound C
    (cmp99Eq389SourceLocalizationOwner L K Q depth)
    (cmp99Eq389SourceLocalizationOwner L K Q depth)
    finBoxDist A rate

end

end YangMills.RG
