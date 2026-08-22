/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpBlockLocalizedSup

/-!
# PRE-VALIDATION: monotonicity of block-localized sup bounds

This source is present, its `.olean` has not yet been materialized, and the
declaration below has not yet been verified by the Lean compiler.

The terminal CMP99 (3.42) assembler needs to enlarge a normalized amplitude
and retain any smaller positive decay rate.  The change is elementary but is
kept as a named theorem so that no rate dictionary is hidden in `simpa`.
-/

namespace YangMills.RG

noncomputable section

/-- A block-localized supremum estimate survives increasing its amplitude and
decreasing its positive exponential rate. -/
theorem finitePiLpTypedBlockLocalizedSupBound_mono
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {sourceOwner : ι → β} {targetOwner : κ → β}
    {dist : β → β → ℕ} {A A' decay rate : ℝ}
    (hC : FinitePiLpTypedBlockLocalizedSupBound C sourceOwner targetOwner
      dist A decay)
    (hA : A ≤ A') (hrate : 0 < rate) (hrate_decay : rate ≤ decay) :
    FinitePiLpTypedBlockLocalizedSupBound C sourceOwner targetOwner
      dist A' rate := by
  refine ⟨hC.1.trans hA, hrate, ?_⟩
  intro owner f hf target
  have hsource := hC.2.2 owner f hf target
  let distance : ℝ := dist (targetOwner target) owner
  have hdistance : 0 ≤ distance := by
    dsimp [distance]
    positivity
  have hexp :
      Real.exp (-(decay * distance)) ≤
        Real.exp (-(rate * distance)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hrate_decay hdistance)
  have hamplitude :
      A * Real.exp (-(decay * distance)) ≤
        A' * Real.exp (-(rate * distance)) := by
    calc
      A * Real.exp (-(decay * distance)) ≤
          A * Real.exp (-(rate * distance)) :=
        mul_le_mul_of_nonneg_left hexp hC.1
      _ ≤ A' * Real.exp (-(rate * distance)) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
  calc
    ‖C f target‖ ≤
        A * Real.exp (-(decay * distance)) * finitePiLpSupNorm f := by
      simpa [distance] using hsource
    _ ≤ A' * Real.exp (-(rate * distance)) * finitePiLpSupNorm f :=
      mul_le_mul_of_nonneg_right hamplitude (finitePiLpSupNorm_nonneg f)

end

end YangMills.RG
