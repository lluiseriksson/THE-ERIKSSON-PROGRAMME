/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4RadialPackage
import YangMills.RG.BalabanCMP109ConstraintCorrectedFluctuation
import YangMills.RG.BalabanCMP96ConstraintNorm

/-!
# Coupling-scaled third jets for the literal equation-(80) potential

The physical CMP109 fluctuation entering the CMP102 potential is `g_k C B`,
not the bare fine field `B`.  This file makes that precomposition literal
and proves that its third iterated derivative carries the expected factor
`|g_k|^3 ‖C‖^3`.  Combining this identity with the volume-uniform bound on
`C` exposes an explicit `|g_k|^3` factor.

This is a scaling bridge only.  It does not identify the resulting cubic
residual with `V''_k`, prove (1.36), or discharge the cutoff-supported
`potential_bound` of the CMP116 terminal source.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

set_option synthInstance.maxHeartbeats 200000

private abbrev CoupledField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The continuous-linear realization of the physical CMP109 field
`B ↦ g_k C B` in the equation-(80) fine-field coordinates. -/
noncomputable def cmp109ConstrainedLinearFluctuationCLM
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) : CoupledField M Q Nc →L[ℝ] CoupledField M Q Nc :=
  gk • cmp96ConstraintEliminationCLM
    (d := 4) (L := M) (N' := 2 * Q) (Nc := Nc)

@[simp]
theorem cmp109ConstrainedLinearFluctuationCLM_apply
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (B : CoupledField M Q Nc) :
    cmp109ConstrainedLinearFluctuationCLM
        (M := M) (Q := Q) (Nc := Nc) gk B =
      cmp109ConstrainedLinearFluctuation (L := M) gk B := by
  simp [cmp109ConstrainedLinearFluctuationCLM,
    cmp109ConstrainedLinearFluctuation]

/-- Precompose an equation-(80) potential with the literal constrained
linear fluctuation `g_k C B`. -/
noncomputable def cmp102Eq80CouplingScaledPotential
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledField M Q Nc → ℝ)
    (B : CoupledField M Q Nc) : ℝ :=
  f (cmp109ConstrainedLinearFluctuationCLM
    (M := M) (Q := Q) (Nc := Nc) gk B)

/-- Exact third-jet chain rule for the physical precomposition. -/
theorem iteratedFDeriv_three_cmp102Eq80CouplingScaledPotential
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledField M Q Nc → ℝ)
    (hf : ContDiff ℝ 3 f) (B : CoupledField M Q Nc) :
    iteratedFDeriv ℝ 3
        (cmp102Eq80CouplingScaledPotential gk f) B =
      (iteratedFDeriv ℝ 3 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B)).compContinuousLinearMap
        (fun _ =>
          cmp109ConstrainedLinearFluctuationCLM
            (M := M) (Q := Q) (Nc := Nc) gk) := by
  change iteratedFDeriv ℝ 3
      (f ∘ cmp109ConstrainedLinearFluctuationCLM
        (M := M) (Q := Q) (Nc := Nc) gk) B = _
  simpa using
    ContinuousLinearMap.iteratedFDeriv_comp_right
      (cmp109ConstrainedLinearFluctuationCLM
        (M := M) (Q := Q) (Nc := Nc) gk)
      hf B (i := 3) le_rfl

/-- The third jet of the precomposed potential is bounded by the original
third jet times the cube of the physical linear-map norm. -/
theorem norm_iteratedFDeriv_three_cmp102Eq80CouplingScaledPotential_le
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledField M Q Nc → ℝ)
    (hf : ContDiff ℝ 3 f) (B : CoupledField M Q Nc) :
    ‖iteratedFDeriv ℝ 3
        (cmp102Eq80CouplingScaledPotential gk f) B‖ ≤
      ‖iteratedFDeriv ℝ 3 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B)‖ *
        ‖cmp109ConstrainedLinearFluctuationCLM
          (M := M) (Q := Q) (Nc := Nc) gk‖ ^ 3 := by
  rw [iteratedFDeriv_three_cmp102Eq80CouplingScaledPotential gk f hf B]
  simpa using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ 3 f
        (cmp109ConstrainedLinearFluctuation (L := M) gk B))
      (fun _ =>
        cmp109ConstrainedLinearFluctuationCLM
          (M := M) (Q := Q) (Nc := Nc) gk)

/-- Volume-uniform operator-norm bound for the physical precomposition.
The coupling appears explicitly and is not hidden in a free constant. -/
theorem norm_cmp109ConstrainedLinearFluctuationCLM_le
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) :
    ‖cmp109ConstrainedLinearFluctuationCLM
        (M := M) (Q := Q) (Nc := Nc) gk‖ ≤
      |gk| * (1 + (M : ℝ) ^ 3) := by
  calc
    ‖cmp109ConstrainedLinearFluctuationCLM
        (M := M) (Q := Q) (Nc := Nc) gk‖
        ≤ |gk| *
          ‖cmp96ConstraintEliminationCLM
            (d := 4) (L := M) (N' := 2 * Q) (Nc := Nc)‖ := by
          simpa [cmp109ConstrainedLinearFluctuationCLM, Real.norm_eq_abs] using
            norm_smul_le gk
              (cmp96ConstraintEliminationCLM
                (d := 4) (L := M) (N' := 2 * Q) (Nc := Nc))
    _ ≤ |gk| * (1 + (M : ℝ) ^ 3) := by
      gcongr
      simpa using
        (norm_cmp96ConstraintEliminationCLM_le
          (d := 4) (L := M) (N' := 2 * Q) (Nc := Nc) (by omega))

/-- Exact scalar cancellation between the cubic coupling factor and the
printed small-field radius `epsilon1 / gk`. -/
theorem coupling_cube_mul_threshold_cube
    (gk epsilon1 constraintCost : ℝ) (hgk : 0 < gk) :
    (|gk| * constraintCost) ^ 3 * (epsilon1 / gk) ^ 3 =
      constraintCost ^ 3 * epsilon1 ^ 3 := by
  rw [abs_of_pos hgk]
  field_simp [ne_of_gt hgk]

/-- Source-facing transport: a bound for the original third jet at the
physical field `g_k C B` yields a bound for the Gaussian-coordinate third
jet with the explicit factor `|g_k|^3`. -/
theorem norm_iteratedFDeriv_three_cmp102Eq80CouplingScaledPotential_le_of_source
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledField M Q Nc → ℝ)
    (hf : ContDiff ℝ 3 f) (B : CoupledField M Q Nc)
    (sourceMajorant : ℝ)
    (hsource :
      ‖iteratedFDeriv ℝ 3 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B)‖ ≤
        sourceMajorant) :
    ‖iteratedFDeriv ℝ 3
        (cmp102Eq80CouplingScaledPotential gk f) B‖ ≤
      sourceMajorant * (|gk| * (1 + (M : ℝ) ^ 3)) ^ 3 := by
  have hsourceMajorant0 : 0 ≤ sourceMajorant :=
    (norm_nonneg
      (iteratedFDeriv ℝ 3 f
        (cmp109ConstrainedLinearFluctuation (L := M) gk B))).trans hsource
  calc
    ‖iteratedFDeriv ℝ 3
        (cmp102Eq80CouplingScaledPotential gk f) B‖
        ≤ ‖iteratedFDeriv ℝ 3 f
            (cmp109ConstrainedLinearFluctuation (L := M) gk B)‖ *
          ‖cmp109ConstrainedLinearFluctuationCLM
            (M := M) (Q := Q) (Nc := Nc) gk‖ ^ 3 :=
      norm_iteratedFDeriv_three_cmp102Eq80CouplingScaledPotential_le
        gk f hf B
    _ ≤ sourceMajorant *
          (|gk| * (1 + (M : ℝ) ^ 3)) ^ 3 := by
      gcongr
      exact norm_cmp109ConstrainedLinearFluctuationCLM_le
        (M := M) (Q := Q) (Nc := Nc) gk

/-- The packaged equation-(80) potential evaluated on the literal physical
CMP109 constrained fluctuation. -/
noncomputable def CMP102Eq80SourcePi4RadialPackage.couplingScaledPhysicalPotential
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (P : CMP102Eq80SourcePi4RadialPackage M Q Nc R Δ)
    (gk : ℝ) (B : CoupledField M Q Nc) : ℝ :=
  cmp102Eq80CouplingScaledPotential gk P.physicalPotential B

end

end YangMills.RG
