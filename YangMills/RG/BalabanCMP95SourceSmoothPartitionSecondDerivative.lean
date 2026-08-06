/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95SourceSmoothPartitionProfile
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# PRE-VALIDATION: derived second-derivative budget for the CMP95 profile

The source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the Lean compiler.

The cutoff-Laplacian term in CMP96 (2.40) is multiplied by the value component
of the regional Green estimate, whose physical scale is quadratic.  The
source profile therefore needs a second-difference estimate at the square of
the cutoff scale.  This module does not add a free profile constant: compact
support and the already recorded `ContDiff` regularity produce a finite global
second-derivative budget by noncomputable choice.

This is only a profile-level analytic input.  Transport through the periodic
cutoff construction, the tensor product, and the physical torus remains open.
-/

namespace YangMills.RG

noncomputable section

namespace CMP95SourceSmoothPartitionProfile

/-- The selected smooth source profile has compact support. -/
theorem hasCompactSupport
    (P : CMP95SourceSmoothPartitionProfile) :
    HasCompactSupport P.value := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (-(2 / 3 : ℝ)) (2 / 3)))
  exact P.support_subset.trans Set.Ioo_subset_Icc_self

/-- Smooth compact support supplies some finite global second-derivative
budget.  This is existence of a bound for the selected profile, not a new
analytic hypothesis. -/
theorem exists_secondDerivBound
    (P : CMP95SourceSmoothPartitionProfile) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖iteratedDeriv 2 P.value t‖ ≤ C := by
  have hcontinuous :
      Continuous (fun t => iteratedFDeriv ℝ 2 P.value t) :=
    P.contDiff.continuous_iteratedFDeriv (by simp)
  have hcompact :
      HasCompactSupport (fun t => iteratedFDeriv ℝ 2 P.value t) :=
    P.hasCompactSupport.iteratedFDeriv 2
  obtain ⟨C, hC⟩ :=
    hcontinuous.bounded_above_of_compact_support hcompact
  refine ⟨max 0 C, le_max_left 0 C, fun t => ?_⟩
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hC t).trans (le_max_right 0 C)

/-- Canonical finite second-derivative budget selected from compactness. -/
noncomputable def secondDerivBound
    (P : CMP95SourceSmoothPartitionProfile) : ℝ :=
  Classical.choose P.exists_secondDerivBound

theorem secondDerivBound_nonneg
    (P : CMP95SourceSmoothPartitionProfile) :
    0 ≤ P.secondDerivBound :=
  (Classical.choose_spec P.exists_secondDerivBound).1

theorem norm_iteratedDeriv_two_le_secondDerivBound
    (P : CMP95SourceSmoothPartitionProfile) (t : ℝ) :
    ‖iteratedDeriv 2 P.value t‖ ≤ P.secondDerivBound :=
  (Classical.choose_spec P.exists_secondDerivBound).2 t

end CMP95SourceSmoothPartitionProfile

end

end YangMills.RG
