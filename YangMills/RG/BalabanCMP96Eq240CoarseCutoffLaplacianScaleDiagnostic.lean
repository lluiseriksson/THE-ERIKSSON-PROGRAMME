/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96Eq240SourceSeparatedCutoffLaplacian

/-!
# Scale diagnostic for the coarse cutoff-Laplacian bound

Compiler-verified at exact source checkpoint
`aaafae326ab952d990c0efb6a66553f0d2a61add` by cold GitHub Actions run
`31067778196`.  The run restored no project `.lake/build` cache; the focal
completed 8,518 jobs and the audited declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.

The previously sealed cutoff-Laplacian theorem is algebraically correct, but
it estimates the discrete Laplacian by eight first differences.  CMP99 (3.42)
multiplies this coefficient by a regional-Green value budget of scale
`B0 * ell^2`, where `ell = L^(depth+1)`.  The exact composition below retains
one positive power of `ell`:

`8 * coarseBudget * (B0 * ell^2) = 32 * B0 * derivBound * ell / K`.

Thus that first-difference majorant is not the physical depth-uniform
`O(K^-1)` estimate printed in CMP96 (2.44)/CMP99 (3.89).  This theorem does
not refute the literal cutoff-Laplacian term; it refutes only this coarse
majorant as its uniform producer.  The faithful repair must use the smooth
second-difference scale before multiplying by the Green value estimate.
-/

namespace YangMills.RG

noncomputable section

variable {L K : ℕ} [NeZero L] [NeZero K]

/-- Exact leftover RG scale in the coarse first-difference majorant. -/
theorem cmp96CoarseCutoffLaplacianBudget_mul_greenValueScale
    (P : CMP95SourceSmoothPartitionProfile)
    (B0 : ℝ) (L K depth : ℕ) [NeZero L] [NeZero K] :
    (8 * cmp96SourceSeparatedCutoffDifferenceBudget P L K depth) *
        (B0 * (L ^ (depth + 1) : ℝ) ^ 2) =
      (32 * B0 * P.derivBound * (L ^ (depth + 1) : ℝ)) / (K : ℝ) := by
  calc
    (8 * cmp96SourceSeparatedCutoffDifferenceBudget P L K depth) *
        (B0 * (L ^ (depth + 1) : ℝ) ^ 2) =
      B0 *
        ((8 * cmp96SourceSeparatedCutoffDifferenceBudget P L K depth) *
          (L ^ (depth + 1) : ℝ)) *
        (L ^ (depth + 1) : ℝ) := by ring
    _ = B0 * ((32 * P.derivBound) / (K : ℝ)) *
        (L ^ (depth + 1) : ℝ) := by
      rw [cmp96SourceSeparatedCutoffLaplacianBudget_mul_generatedRange]
    _ = (32 * B0 * P.derivBound *
        (L ^ (depth + 1) : ℝ)) / (K : ℝ) := by ring

end

end YangMills.RG
