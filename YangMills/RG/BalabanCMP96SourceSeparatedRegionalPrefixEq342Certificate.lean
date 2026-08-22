/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixLeftDerivativeOwnerDecay
import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixGreenBlockLocalizedOwnerDecay
import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixLaplacianOwnerDecay
import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixRightAdjointOwnerDecay
import YangMills.RG.BalabanCMP99Eq342CommonAmplitude
import YangMills.RG.FinitePiLpBlockLocalizedSupMonotone

/-!
# Per-depth physical CMP99 (3.42) certificate

The theorem is not the uniform C6c.9 endpoint: its common amplitude and rate
still depend on `depth`.  In particular it must not be cited as the uniform
`B0, delta0` producer required by CMP99 (3.42).

The terminal derivative spacing is definitionally
`L^(depth+1) * spacing`; using the base spacing here would construct a
different operator even though the generic certificate accepts either real
parameter.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Per-depth assembly of the four literal physical P8 actions into the
source-localized CMP99 (3.42) record.  This is a scalar assembler, not a
uniform-in-depth estimate. -/
theorem cmp96SourceSeparatedRegionalPrefix_eq342SourceLocalizedGreenCertificate
    (P : CMP95SourceSmoothPartitionProfile)
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a decay : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a) (hdecay : 0 < decay)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q)
    (root : ActiveGaugeRegion.Site
      (cmp96SourceSeparatedRegionalCell P L K Q depth cell)) :
    letI : Nonempty (ActiveGaugeRegion.Site
      (cmp96SourceSeparatedRegionalCell P L K Q depth cell)) := ⟨root⟩
    let ell := L ^ (depth + 1)
    let upper := cmp89SourceSeparatedPrefixPrecisionUpperBound
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall *
      Real.exp (decay * (ell : ℕ))
    let coercivity := cmp89SourceSeparatedPrefixCoercivity
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
      spacing epsilon a background budget fineSmall
    let rate := finitePiLpExponentialInverseDecayRate upper decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) coercivity
    let ownerRate := (ell : ℝ) * rate
    let valueAmplitude := (2 / coercivity) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    let leftAmplitude := valueAmplitude *
      ((1 + Real.exp ownerRate) / spacing)
    let rightAmplitude :=
      648 * valueAmplitude * Real.exp ownerRate / spacing
    let laplacianAmplitude := 4 * leftAmplitude *
      ((1 + Real.exp ownerRate) / spacing)
    let B0 := cmp99Eq342CommonAmplitude valueAmplitude leftAmplitude
      rightAmplitude laplacianAmplitude
    CMP99Eq342SourceLocalizedGreenCertificate
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      depth (cmp96SourceSeparatedRegionalCell P L K Q depth cell)
      (matrixSUNAdjointModel Nc)
      (cmp99Eq389SourceSeparatedPhysicalBackground
        L K Q depth Nc background)
      ((ell : ℝ) * spacing)
      (cmp89SourceSeparatedAmbientPrefixPrecision hL depth
        spacing epsilon a background budget fineSmall)
      coercivity
      (cmp89SourceSeparatedPrefixCoercivity_pos hL depth hspacing ha
        background budget fineSmall hsmall)
      (isCoerciveCLM_cmp89SourceSeparatedAmbientPrefixPrecision
        hL depth hspacing ha background budget fineSmall hsmall)
      B0 ownerRate := by
  dsimp only
  let Omega := cmp96SourceSeparatedRegionalCell P L K Q depth cell
  let ell := L ^ (depth + 1)
  let upper := cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
      spacing epsilon a background budget fineSmall *
    Real.exp (decay * (ell : ℕ))
  let coercivity := cmp89SourceSeparatedPrefixCoercivity hL depth
    spacing epsilon a background budget fineSmall
  let rate := finitePiLpExponentialInverseDecayRate upper decay
    (cmp99OmegaSiteExpSumBound (decay / 4)) coercivity
  let ownerRate := (ell : ℝ) * rate
  let valueAmplitude := (2 / coercivity) *
    Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
  let leftAmplitude := valueAmplitude *
    ((1 + Real.exp ownerRate) / spacing)
  let rightAmplitude :=
    648 * valueAmplitude * Real.exp ownerRate / spacing
  let laplacianAmplitude := 4 * leftAmplitude *
    ((1 + Real.exp ownerRate) / spacing)
  let B0 := cmp99Eq342CommonAmplitude valueAmplitude leftAmplitude
    rightAmplitude laplacianAmplitude
  letI : Nonempty (ActiveGaugeRegion.Site Omega) := ⟨root⟩
  have hell : 0 < (ell : ℝ) := by
    have hellNat : 0 < ell := pow_pos (NeZero.pos L) (depth + 1)
    exact_mod_cast hellNat
  have hcoercivity : 0 < coercivity := by
    exact cmp89SourceSeparatedPrefixCoercivity_pos hL depth hspacing ha
      background budget fineSmall hsmall
  have hupper : 0 ≤ upper := by
    exact mul_nonneg
      (cmp89SourceSeparatedPrefixPrecisionUpperBound_pos hL depth
        hspacing background budget fineSmall).le
      (Real.exp_pos _).le
  have hrow : 0 ≤ cmp99OmegaSiteExpSumBound (decay / 4) := by
    unfold cmp99OmegaSiteExpSumBound
    positivity
  have hrate : 0 < rate :=
    finitePiLpExponentialInverseDecayRate_pos
      hupper hdecay hrow hcoercivity
  have hownerRate : 0 < ownerRate := mul_pos hell hrate
  have hvalueAmplitude : 0 ≤ valueAmplitude := by
    dsimp [valueAmplitude]
    positivity
  have hleftAmplitude : 0 ≤ leftAmplitude := by
    dsimp [leftAmplitude]
    positivity
  have hrightAmplitude : 0 ≤ rightAmplitude := by
    dsimp [rightAmplitude]
    positivity
  have hlaplacianAmplitude : 0 ≤ laplacianAmplitude := by
    dsimp [laplacianAmplitude]
    positivity
  have hB0 : 0 < B0 := by
    exact cmp99Eq342CommonAmplitude_pos hvalueAmplitude hleftAmplitude
      hrightAmplitude hlaplacianAmplitude
  have hvalue0 :=
    cmp96SourceSeparatedRegionalPrefixGreen_blockLocalizedSupBound
      P hL depth hspacing ha hdecay background budget fineSmall hsmall
      cell root
  have hleft0 :=
    cmp96SourceSeparatedRegionalPrefixLeftDerivative_blockLocalizedSupBound
      P hL depth hspacing ha hdecay background budget fineSmall hsmall
      cell root
  have hright0 :=
    cmp96SourceSeparatedRegionalPrefixRightAdjoint_blockLocalizedSupBound
      P hL depth hspacing ha hdecay background budget fineSmall hsmall
      cell root
  have hlaplacian0 :=
    cmp96SourceSeparatedRegionalPrefixLaplacian_blockLocalizedSupBound
      P hL depth hspacing ha hdecay background budget fineSmall hsmall
      cell root
  refine {
    B0_pos := hB0
    delta0_pos := hownerRate
    value_bound := ?_
    left_derivative_bound := ?_
    right_adjoint_derivative_bound := ?_
    laplacian_bound := ?_
  }
  · apply finitePiLpTypedBlockLocalizedSupBound_mono hvalue0
    · simpa only [ell, upper, coercivity, rate, ownerRate,
        valueAmplitude, leftAmplitude, rightAmplitude, laplacianAmplitude,
        B0, Nat.cast_pow] using
        (mul_le_mul_of_nonneg_right
          (le_cmp99Eq342CommonAmplitude_value hvalueAmplitude hleftAmplitude
            hrightAmplitude hlaplacianAmplitude)
          (sq_nonneg (ell : ℝ)))
    · exact hownerRate
    · exact le_rfl
  · apply finitePiLpTypedBlockLocalizedSupBound_mono hleft0
    · simpa only [ell, upper, coercivity, rate, ownerRate,
        valueAmplitude, leftAmplitude, rightAmplitude, laplacianAmplitude,
        B0, Nat.cast_pow] using
        (mul_le_mul_of_nonneg_right
          (le_cmp99Eq342CommonAmplitude_left hvalueAmplitude hleftAmplitude
            hrightAmplitude hlaplacianAmplitude)
          hell.le)
    · exact hownerRate
    · exact le_rfl
  · apply finitePiLpTypedBlockLocalizedSupBound_mono hright0
    · simpa only [ell, upper, coercivity, rate, ownerRate,
        valueAmplitude, leftAmplitude, rightAmplitude, laplacianAmplitude,
        B0, Nat.cast_pow] using
        (mul_le_mul_of_nonneg_right
          (le_cmp99Eq342CommonAmplitude_right hvalueAmplitude hleftAmplitude
            hrightAmplitude hlaplacianAmplitude)
          hell.le)
    · exact hownerRate
    · exact le_rfl
  · apply finitePiLpTypedBlockLocalizedSupBound_mono hlaplacian0
    · exact le_cmp99Eq342CommonAmplitude_laplacian
        hvalueAmplitude hleftAmplitude hrightAmplitude hlaplacianAmplitude
    · exact hownerRate
    · exact le_rfl

end

end YangMills.RG
