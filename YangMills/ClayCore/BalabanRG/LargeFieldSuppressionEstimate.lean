import Mathlib
import YangMills.ClayCore.BalabanRG.P80EstimateSkeleton

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# LargeFieldSuppressionEstimate — Layer 11E

Isolates the P80 large-field estimate under a precise theorem name.

In the current repository semantics this is now dischargeable from the already-green
P80 skeleton, because `RGBlockingMap` is still the zero map and the required
large-field decomposition steps are already formalized there.
-/

noncomputable section

/-- The P80 large-field estimate. Source: P80 §4 (Balaban large-field suppression).
Content: outside small-field regime, RG remainder is exponentially suppressed. -/
theorem large_field_remainder_bound_P80
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) (hβ : 1 ≤ β) :
    LargeFieldSuppressionBound d N_c β := by
  exact
    large_field_suppression_from_P80_steps d N_c β hβ
      (fun k =>
        large_field_decomposition_P80_step1 d N_c β hβ k)
      (fun k split h_lf K =>
        large_field_exponential_suppression_P80_step2 d N_c β hβ k split h_lf K)

/-- Wrapper: this is the version called from RGContractiveEstimate. -/
theorem large_field_suppression_bound_v2
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) (hβ : 1 ≤ β) :
    LargeFieldSuppressionBound d N_c β :=
  large_field_remainder_bound_P80 d N_c β hβ

end

end YangMills.ClayCore
