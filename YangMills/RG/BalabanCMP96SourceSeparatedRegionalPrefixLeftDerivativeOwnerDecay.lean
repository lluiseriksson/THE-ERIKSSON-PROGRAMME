/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixRescaledOwnerDecay
import YangMills.RG.BalabanCMP99Eq389BlockShiftGeometry
import YangMills.RG.BalabanCMP99Eq389ThreeSpeciesPhysicalBound

/-!
# Physical P8 left-derivative owner decay

CMP99 (3.42) gives the left-derivative Green the scale `ell`, rather than the
`ell^2` of the Green itself.  Here `ell = L^(depth+1)`.  The reduction is
literal: the physical covariant derivative is evaluated at the terminal RG
spacing `ell * spacing`, as fixed by
`cmp89SourceSeparatedPrefixTower_terminalSpacing`.

The two endpoint values are bounded by the already sealed rescaled-owner
Green estimate.  Moving the positive endpoint by one fine link costs the
explicit factor `exp ownerRate`; adjoint transport is norm preserving.  Thus
the displayed amplitude is

`ownerAmplitude * ((1 + exp ownerRate) / spacing) * ell`.

This remains a per-depth estimate.  It neither produces uniform `B0` and
`delta0` nor claims the complete CMP99 (3.42) certificate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroPrefixLeftDerivativeAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

private instance instNeZeroPrefixLeftDerivativeSourceSide
    (K Q : ℕ) [NeZero K] [NeZero Q] :
    NeZero (2 * (K * Q)) :=
  ⟨(Nat.mul_pos (by omega)
    (Nat.mul_pos (NeZero.pos K) (NeZero.pos Q))).ne'⟩

private instance instNeZeroPrefixLeftDerivativeFineSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (L ^ (depth + 1) * (2 * (K * Q))) :=
  ⟨(Nat.mul_pos (pow_pos (NeZero.pos L) (depth + 1))
    (Nat.mul_pos (by omega)
      (Nat.mul_pos (NeZero.pos K) (NeZero.pos Q)))).ne'⟩

private theorem finBoxEquivCast_shift
    {d N M : ℕ} [NeZero N] [NeZero M]
    (h : N = M) (x : FinBox d N) (i : Fin d) :
    Equiv.cast (congrArg (FinBox d) h) (x.shift i) =
      (Equiv.cast (congrArg (FinBox d) h) x).shift i := by
  subst M
  rfl

/-- A positive fine step costs at most one `exp(delta)` in the literal
source-localization owner metric. -/
theorem exp_neg_sourceLocalizationOwner_shift_le_exp_mul
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (owner : FinBox 4 (2 * (K * Q))) (i : Fin 4)
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    Real.exp (-(delta *
        (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shift i))
          owner : ℝ))) ≤
      Real.exp delta * Real.exp (-(delta *
        (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
          owner : ℝ))) := by
  have hcastShift :
      cmp99Eq389SourceLocalizationSiteEquiv L K Q depth (x.shift i) =
        (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth x).shift i := by
    exact finBoxEquivCast_shift
      (cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier L K Q depth)
      x i
  have hstepBack := finBoxDist_blockSite_shiftBack_le_one
    (m := L ^ (depth + 1)) (n := 2 * (K * Q))
    ((cmp99Eq389SourceLocalizationSiteEquiv L K Q depth x).shift i) i
  have hstep :
      finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth x)
          (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shift i)) ≤ 1 := by
    simpa [cmp99Eq389SourceLocalizationOwner, hcastShift,
      FinBox.shiftBack_shift, finBoxDist_comm] using hstepBack
  have hdist :
      finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x) owner ≤
        1 + finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shift i))
          owner :=
    (finBoxDist_triangle
      (cmp99Eq389SourceLocalizationOwner L K Q depth x)
      (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shift i))
      owner).trans (Nat.add_le_add_right hstep _)
  have hdistR :
      (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
          owner : ℝ) ≤
        1 + (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shift i))
          owner : ℝ) := by
    exact_mod_cast hdist
  have harg :
      -(delta * (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shift i))
          owner : ℝ)) ≤
        delta + -(delta *
          (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
            owner : ℝ)) := by
    nlinarith
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr harg

/-- The literal terminal-spacing covariant derivative of the physical P8
Green has the `ell` scale and the same block-rescaled owner rate.

The arbitrary source owner is not assumed to be represented in the active
carrier.  When its fibre is empty, the support hypothesis forces the input
field to vanish; otherwise the representing root is constructed internally.
-/
theorem cmp96SourceSeparatedRegionalPrefixLeftDerivative_blockLocalizedSupBound
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
    let A := cmp89SourceSeparatedPrefixPrecisionUpperBound
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall *
      Real.exp (decay * (ell : ℕ))
    let c := cmp89SourceSeparatedPrefixCoercivity
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
      spacing epsilon a background budget fineSmall
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    let ownerRate := (ell : ℝ) * rate
    let ownerAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    let leftAmplitude := ownerAmplitude *
      ((1 + Real.exp ownerRate) / spacing)
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM
          (cmp96SourceSeparatedRegionalCell P L K Q depth cell)
          (matrixSUNAdjointModel Nc)
          (cmp99Eq389SourceSeparatedPhysicalBackground
            L K Q depth Nc background) ((ell : ℝ) * spacing)).comp
        (cmp96SourceSeparatedRegionalPrefixGreen
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          P hL depth hspacing ha background budget fineSmall hsmall cell))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      finBoxDist (leftAmplitude * (ell : ℝ)) ownerRate := by
  dsimp only
  let Omega := cmp96SourceSeparatedRegionalCell P L K Q depth cell
  let ell := L ^ (depth + 1)
  let Cregional := cmp96SourceSeparatedRegionalPrefixGreen
    P hL depth hspacing ha background budget fineSmall hsmall cell
  let A := cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
      spacing epsilon a background budget fineSmall *
    Real.exp (decay * (ell : ℕ))
  let c := cmp89SourceSeparatedPrefixCoercivity hL depth
    spacing epsilon a background budget fineSmall
  let rate := finitePiLpExponentialInverseDecayRate A decay
    (cmp99OmegaSiteExpSumBound (decay / 4)) c
  let ownerRate := (ell : ℝ) * rate
  let ownerAmplitude := (2 / c) *
    Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
  let leftAmplitude := ownerAmplitude *
    ((1 + Real.exp ownerRate) / spacing)
  let terminalSpacing := (ell : ℝ) * spacing
  let regionalBackground := cmp99Eq389SourceSeparatedPhysicalBackground
    L K Q depth Nc background
  letI : Nonempty (ActiveGaugeRegion.Site Omega) := ⟨root⟩
  have hc : 0 < c := by
    exact cmp89SourceSeparatedPrefixCoercivity_pos hL depth hspacing ha
      background budget fineSmall hsmall
  have hA : 0 ≤ A := by
    exact mul_nonneg
      (cmp89SourceSeparatedPrefixPrecisionUpperBound_pos hL depth
        hspacing background budget fineSmall).le
      (Real.exp_pos _).le
  have hrow : 0 ≤ cmp99OmegaSiteExpSumBound (decay / 4) := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hrate : 0 < rate := by
    exact finitePiLpExponentialInverseDecayRate_pos hA hdecay hrow hc
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (depth + 1)
  have hterminal : 0 < terminalSpacing := mul_pos hell hspacing
  have hownerAmplitude : 0 ≤ ownerAmplitude := by
    exact mul_nonneg (div_nonneg (by positivity) hc.le) (Real.exp_pos _).le
  have hleftAmplitude : 0 ≤ leftAmplitude := by
    exact mul_nonneg hownerAmplitude
      (div_nonneg (add_nonneg zero_le_one (Real.exp_pos _).le) hspacing.le)
  refine ⟨mul_nonneg hleftAmplitude hell.le, mul_pos hell hrate, ?_⟩
  intro owner f hf bond
  by_cases howner : ∃ source : ActiveGaugeRegion.Site Omega,
      cmp99Eq342SourceLocalizedActiveOwner L K Q depth source = owner
  · rcases howner with ⟨source, hsource⟩
    let phi := Cregional f
    let extPhi := extendZeroZeroCLM Omega phi
    have hvalue (x : FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
        ‖extPhi x‖ ≤
          (ownerAmplitude * (ell : ℝ) ^ 2) *
            Real.exp (-(ownerRate *
              (finBoxDist
                (cmp99Eq389SourceLocalizationOwner L K Q depth x)
                owner : ℝ))) * finitePiLpSupNorm f := by
      by_cases hx : x ∈ Omega.sites
      · let target : ActiveGaugeRegion.Site Omega := ⟨x, hx⟩
        have hbase :=
          norm_cmp96SourceSeparatedRegionalPrefixGreen_apply_le_rescaledOwnerScale
            P hL depth hspacing ha hdecay background budget fineSmall hsmall
            cell owner source hsource f hf target
        simpa [phi, extPhi, Cregional,
          extendZeroZeroCLM_apply_of_mem Omega phi x hx,
          cmp99Eq342SourceLocalizedActiveOwner, target,
          ell, A, c, rate, ownerRate, ownerAmplitude,
          finBoxDist_comm] using hbase
      · rw [show extPhi x = 0 by
          exact extendZeroZeroCLM_apply_of_not_mem Omega phi x hx, norm_zero]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg hownerAmplitude (sq_nonneg _))
            (Real.exp_pos _).le)
          (finitePiLpSupNorm_nonneg f)
    have hshift := hvalue (bond.1.shift bond.2)
    have hshiftExp := exp_neg_sourceLocalizationOwner_shift_le_exp_mul
      L K Q depth bond.1 owner bond.2 (delta := ownerRate)
        (mul_pos hell hrate).le
    have hshiftValue :
        ‖extPhi (bond.1.shift bond.2)‖ ≤
          (ownerAmplitude * (ell : ℝ) ^ 2) *
            (Real.exp ownerRate * Real.exp (-(ownerRate *
              (finBoxDist
                (cmp99Eq389SourceLocalizationOwner L K Q depth bond.1)
                owner : ℝ)))) * finitePiLpSupNorm f := by
      calc
        ‖extPhi (bond.1.shift bond.2)‖ ≤
            (ownerAmplitude * (ell : ℝ) ^ 2) *
              Real.exp (-(ownerRate *
                (finBoxDist
                  (cmp99Eq389SourceLocalizationOwner L K Q depth
                    (bond.1.shift bond.2)) owner : ℝ))) *
              finitePiLpSupNorm f := hshift
        _ ≤ (ownerAmplitude * (ell : ℝ) ^ 2) *
            (Real.exp ownerRate * Real.exp (-(ownerRate *
              (finBoxDist
                (cmp99Eq389SourceLocalizationOwner L K Q depth bond.1)
                owner : ℝ)))) * finitePiLpSupNorm f := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hshiftExp
              (mul_nonneg hownerAmplitude (sq_nonneg _)))
            (finitePiLpSupNorm_nonneg f)
    have hfirst := hvalue bond.1
    change ‖terminalSpacing⁻¹ •
      (extPhi bond.1 -
        (matrixSUNAdjointModel Nc).adCLM
          (regionalBackground (ConcreteEdge.mk bond.1 bond.2 true))
          (extPhi (bond.1.shift bond.2)))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hterminal)]
    calc
      terminalSpacing⁻¹ *
          ‖extPhi bond.1 -
                (matrixSUNAdjointModel Nc).adCLM
                (regionalBackground (ConcreteEdge.mk bond.1 bond.2 true))
              (extPhi (bond.1.shift bond.2))‖ ≤
        terminalSpacing⁻¹ *
          (‖extPhi bond.1‖ + ‖extPhi (bond.1.shift bond.2)‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hterminal.le)
        calc
          ‖extPhi bond.1 -
              (matrixSUNAdjointModel Nc).adCLM
                (regionalBackground (ConcreteEdge.mk bond.1 bond.2 true))
                (extPhi (bond.1.shift bond.2))‖ ≤
            ‖extPhi bond.1‖ +
              ‖(matrixSUNAdjointModel Nc).adCLM
                (regionalBackground (ConcreteEdge.mk bond.1 bond.2 true))
                (extPhi (bond.1.shift bond.2))‖ := norm_sub_le _ _
          _ = ‖extPhi bond.1‖ + ‖extPhi (bond.1.shift bond.2)‖ := by
            rw [(matrixSUNAdjointModel Nc).norm_ad]
      _ ≤ terminalSpacing⁻¹ *
          ((ownerAmplitude * (ell : ℝ) ^ 2) *
              Real.exp (-(ownerRate *
                (finBoxDist
                  (cmp99Eq389SourceLocalizationOwner L K Q depth bond.1)
                  owner : ℝ))) * finitePiLpSupNorm f +
            (ownerAmplitude * (ell : ℝ) ^ 2) *
              (Real.exp ownerRate * Real.exp (-(ownerRate *
                (finBoxDist
                  (cmp99Eq389SourceLocalizationOwner L K Q depth bond.1)
                  owner : ℝ)))) * finitePiLpSupNorm f) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hfirst hshiftValue)
          (inv_nonneg.mpr hterminal.le)
      _ = (leftAmplitude * (ell : ℝ)) *
          Real.exp (-(ownerRate *
            (finBoxDist
              (cmp99Eq342SourceLocalizedBondOwner L K Q depth bond)
              owner : ℝ))) * finitePiLpSupNorm f := by
        dsimp [terminalSpacing, leftAmplitude]
        unfold cmp99Eq342SourceLocalizedBondOwner
        field_simp [ne_of_gt hspacing, ne_of_gt hell]
  · have hfzero : f = 0 := by
      apply PiLp.ext
      intro source
      apply hf source
      intro hsource
      exact howner ⟨source, hsource⟩
    subst f
    have hzero :
        (((cmp99ActiveRegionSourceCovariantD0CLM Omega
            (matrixSUNAdjointModel Nc) regionalBackground terminalSpacing).comp
          Cregional) (0 : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))) bond = 0 := by
      rw [map_zero]
      rfl
    rw [hzero, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hleftAmplitude hell.le)
        (Real.exp_pos _).le)
      (finitePiLpSupNorm_nonneg 0)

end

end YangMills.RG
