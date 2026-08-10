/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalAliasPrecisionMatrix
import YangMills.RG.BalabanCMP99SourceFlatWeightedAdjointPhysicalColumn

/-!
# Fourier orientation of the flat physical weighted adjoint

The forward DFT evaluates the source weighted-adjoint column at the periodic
negative fine momentum.  The physical alias-precision matrix keeps its
direct-momentum column and opposite-momentum row as different objects.  This
module proves, through the literal `ZMod` negation and an exact reciprocal
period, that the DFT output is the printed opposite-momentum row factor.

No abstract self-adjointness exchanges the two orientations.  This module
does not invert the alias matrix, identify flat and interacting transport,
restrict to a regional carrier or produce `B0`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- Periodic negation changes the physical one-block amplitude momentum to
the literal opposite momentum, up to an internally constructed integer
multiple of the exact `2*pi*M` amplitude period. -/
theorem cmp99SourceFlatQprimeAmplitudeMomentum_fourierNeg_eq_neg_add_period
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (k : FinBox d (M * N')) :
    ∃ w : Fin d → ℤ,
      cmp99SourceFlatQprimeAmplitudeMomentum (cmp99FinBoxFourierNeg k) =
        fun mu =>
          -cmp99SourceFlatQprimeAmplitudeMomentum k mu +
            (w mu : ℂ) * (((2 * Real.pi * (M : ℝ) : ℝ) : ℂ)) := by
  let kneg : FinBox d (M * N') := cmp99FinBoxFourierNeg k
  have hcoord (mu : Fin d) :
      (((kneg mu).val : ℕ) : ZMod (M * N')) =
        -(((k mu).val : ℕ) : ZMod (M * N')) := by
    have h := congrFun (cmp99FinBoxZModEquiv_fourierNeg k) mu
    simpa only [cmp99FinBoxZModEquiv_apply, kneg] using h
  have hdiv (mu : Fin d) :
      ((M * N' : ℕ) : ℤ) ∣
        ((kneg mu).val : ℤ) + ((k mu).val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcoord]
    ring
  choose c hc using hdiv
  refine ⟨fun mu => -c mu, ?_⟩
  funext mu
  have hcC := congrArg (fun x : ℤ => (x : ℂ)) (hc mu)
  push_cast at hcC
  have hM : (M : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  have hN : (N' : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N')
  simp only [cmp99SourceFlatQprimeAmplitudeMomentum,
    cmp99FlatDiscreteMomentum]
  push_cast
  field_simp [hM, hN]
  change -(((kneg mu).val : ℕ) : ℂ) =
    (((k mu).val : ℕ) : ℂ) - (M : ℂ) * (N' : ℂ) * (c mu : ℂ)
  linear_combination -hcC

/-- The one-block amplitude at periodic negative Fourier momentum is exactly
the separately named opposite-momentum row amplitude. -/
theorem cmp89Eq245EntireAverageAmplitude_amplitudeMomentum_fourierNeg_eq_neg
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (k : FinBox d (M * N')) :
    cmp89Eq245EntireAverageAmplitude d M
        (cmp99SourceFlatQprimeAmplitudeMomentum
          (cmp99FinBoxFourierNeg k)) =
      cmp89Eq245EntireAverageAmplitude d M
        (-cmp99SourceFlatQprimeAmplitudeMomentum k) := by
  rcases
      cmp99SourceFlatQprimeAmplitudeMomentum_fourierNeg_eq_neg_add_period k with
    ⟨w, hw⟩
  rw [hw]
  exact cmp89Eq245EntireAverageAmplitude_add_int_aliasPeriods
    (Nat.pos_of_ne_zero (NeZero.ne M))
    (-cmp99SourceFlatQprimeAmplitudeMomentum k) w

/-- On one fixed coarse reciprocal fibre, the exact DFT of the literal flat
physical weighted adjoint is the printed opposite-momentum alias row.  The
full fine-volume normalization remains visible. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatWeightedAdjoint_fixedCoarse_eq_aliasRow
    {d M N' Nc : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ell : FinBox d N') (v : SUNLieComplexCoord Nc)
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v) k.1 =
      (((M * N' : ℕ) : ℂ) ^ d *
        cmp89Eq246EntireAliasAverageRow d M 1
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
            d M N' ell k)) • v := by
  rw [cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexWeightedAdjointCoarseMode,
    if_pos k.property]
  rw [cmp89Eq245EntireAverageAmplitude_amplitudeMomentum_fourierNeg_eq_neg,
    cmp99SourceFlatQprimeNegAmplitude_eq_entireAliasRow]

end

end YangMills.RG
