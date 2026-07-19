/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance
import YangMills.RG.BalabanCMP99SourceScaledStratification

/-!
# A source-weighted tower average on one global CMP99 stratum

The adjoint in printed CMP99 (3.25) is taken in lattice-spacing scalar
products.  For a stratum `Lambda_r` it is therefore not the bare counting
adjoint of `S_r Q'_r`.  This file constructs it literally as

`(Q'_r)^dagger L_r^{-1} E_r`,

where `E_r` is zero extension from `Lambda_r` and `L_r` is the isometric
identification of the retained tower level with the source scale lattice.
The exact source normalization then survives restriction and gives the
coercivity of `S_r Q'_r G^2 (Q'_r)^dagger L_r^{-1} E_r` without a free
surjectivity or adjoint lower-bound premise.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

universe u v

variable {d N : ℕ} {g : Type} [NeZero N]
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]
variable {Omega : ActiveGaugeRegion d N} {spacing : ℝ}

namespace CMP99SourceWeightedRegionalTower

variable {FineSite : Type u} [DecidableEq FineSite]
variable {n : ℕ} {ScaleSite : Fin n → Type v}
variable [∀ r, DecidableEq (ScaleSite r)] [∀ r, Fintype (ScaleSite r)]

/-- The literal restricted order-`r` source average. -/
noncomputable def stratumAverage
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n)
    (levelEquiv : T.TerminalSpace.carrier ≃ₗᵢ[ℝ]
      CMP99SourceScaledStratification.ScaleField
        (ScaleSite := ScaleSite) g r) :
    ActiveGaugeZeroCochain Omega g →L[ℝ] S.StratumField g r :=
  (S.restrictStratumCLM r).comp
    (levelEquiv.toContinuousLinearMap.comp T.Qprime)

/-- The printed lattice-spacing adjoint of the restricted average: zero
extend, return through the isometric level dictionary, then apply the exact
weighted synthesis of the source tower. -/
noncomputable def stratumWeightedAdjoint
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n)
    (levelEquiv : T.TerminalSpace.carrier ≃ₗᵢ[ℝ]
      CMP99SourceScaledStratification.ScaleField
        (ScaleSite := ScaleSite) g r) :
    S.StratumField g r →L[ℝ] ActiveGaugeZeroCochain Omega g :=
  T.weightedAdjoint.comp
    (levelEquiv.symm.toContinuousLinearMap.comp (S.extendStratumCLM r))

/-- Restriction and the isometric level dictionary preserve the exact source
coisometry `Q'_r (Q'_r)^dagger = I`. -/
theorem stratumAverage_comp_stratumWeightedAdjoint
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n)
    (levelEquiv : T.TerminalSpace.carrier ≃ₗᵢ[ℝ]
      CMP99SourceScaledStratification.ScaleField
        (ScaleSite := ScaleSite) g r) :
    (T.stratumAverage S r levelEquiv).comp
        (T.stratumWeightedAdjoint S r levelEquiv) =
      ContinuousLinearMap.id ℝ (S.StratumField g r) := by
  apply ContinuousLinearMap.ext
  intro xi
  change S.restrictStratumCLM r
      (levelEquiv
        (T.Qprime
          (T.weightedAdjoint
            (levelEquiv.symm (S.extendStratumCLM r xi))))) = xi
  have hQ := congrArg
    (fun A : T.TerminalSpace.carrier →L[ℝ] T.TerminalSpace.carrier =>
      A (levelEquiv.symm (S.extendStratumCLM r xi)))
    T.Qprime_comp_weightedAdjoint
  change T.Qprime
      (T.weightedAdjoint (levelEquiv.symm (S.extendStratumCLM r xi))) =
    levelEquiv.symm (S.extendStratumCLM r xi) at hQ
  rw [hQ, levelEquiv.apply_symm_apply]
  have hR := congrArg
    (fun A : S.StratumField g r →L[ℝ] S.StratumField g r => A xi)
    (S.restrictStratumCLM_comp_extendStratumCLM (g := g) r)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    using hR

/-- Exact source pairing after restriction to `Lambda_r`. -/
theorem stratumWeightedAdjoint_pairing
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n)
    (levelEquiv : T.TerminalSpace.carrier ≃ₗᵢ[ℝ]
      CMP99SourceScaledStratification.ScaleField
        (ScaleSite := ScaleSite) g r)
    (phi : ActiveGaugeZeroCochain Omega g) (xi : S.StratumField g r) :
    T.terminalSpacing ^ d *
        inner ℝ (T.stratumAverage S r levelEquiv phi) xi =
      spacing ^ d *
        inner ℝ phi (T.stratumWeightedAdjoint S r levelEquiv xi) := by
  let eta := levelEquiv.symm (S.extendStratumCLM r xi)
  have hpair := T.weightedAdjoint_pairing phi eta
  change T.terminalSpacing ^ d * inner ℝ (T.Qprime phi) eta =
    spacing ^ d * inner ℝ phi (T.weightedAdjoint eta) at hpair
  calc
    T.terminalSpacing ^ d *
        inner ℝ (T.stratumAverage S r levelEquiv phi) xi =
      T.terminalSpacing ^ d *
        inner ℝ (levelEquiv (T.Qprime phi))
          (S.extendStratumCLM r xi) := by
            congr 1
            rw [real_inner_comm]
            change inner ℝ xi
                (S.restrictStratumCLM r (levelEquiv (T.Qprime phi))) =
              inner ℝ (levelEquiv (T.Qprime phi))
                (S.extendStratumCLM r xi)
            exact (S.inner_restrictStratumCLM_eq_extendStratumCLM
              r xi (levelEquiv (T.Qprime phi))).trans
                (real_inner_comm _ _)
    _ = T.terminalSpacing ^ d * inner ℝ (T.Qprime phi) eta := by
          congr 1
          have hinner := levelEquiv.inner_map_map (T.Qprime phi) eta
          simpa [eta] using hinner
    _ = spacing ^ d * inner ℝ phi (T.weightedAdjoint eta) := hpair
    _ = spacing ^ d *
        inner ℝ phi (T.stratumWeightedAdjoint S r levelEquiv xi) := rfl

/-- The exact source norm law also survives stratum restriction. -/
theorem stratumWeightedAdjoint_spacingNormSq
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n)
    (levelEquiv : T.TerminalSpace.carrier ≃ₗᵢ[ℝ]
      CMP99SourceScaledStratification.ScaleField
        (ScaleSite := ScaleSite) g r)
    (xi : S.StratumField g r) :
    spacing ^ d * ‖T.stratumWeightedAdjoint S r levelEquiv xi‖ ^ 2 =
      T.terminalSpacing ^ d * ‖xi‖ ^ 2 := by
  change spacing ^ d *
      ‖T.weightedAdjoint
        (levelEquiv.symm (S.extendStratumCLM r xi))‖ ^ 2 = _
  rw [T.weightedAdjoint_spacingNormSq]
  rw [levelEquiv.symm.norm_map, S.norm_extendStratumCLM_eq r xi]

/-- The source-weighted middle covariance on the actual stratum. -/
noncomputable def stratumCoarseCovarianceMiddle
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n)
    (levelEquiv : T.TerminalSpace.carrier ≃ₗᵢ[ℝ]
      CMP99SourceScaledStratification.ScaleField
        (ScaleSite := ScaleSite) g r)
    (G : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g) :
    S.StratumField g r →L[ℝ] S.StratumField g r :=
  (T.stratumAverage S r levelEquiv).comp
    (G.comp (G.comp (T.stratumWeightedAdjoint S r levelEquiv)))

/-- Exact weighted square identity for the stratum covariance. -/
theorem weighted_inner_stratumCoarseCovarianceMiddle
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n)
    (levelEquiv : T.TerminalSpace.carrier ≃ₗᵢ[ℝ]
      CMP99SourceScaledStratification.ScaleField
        (ScaleSite := ScaleSite) g r)
    (G : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    (hG : G.IsSymmetric) (xi : S.StratumField g r) :
    T.terminalSpacing ^ d *
        inner ℝ xi (T.stratumCoarseCovarianceMiddle S r levelEquiv G xi) =
      spacing ^ d *
        ‖G (T.stratumWeightedAdjoint S r levelEquiv xi)‖ ^ 2 := by
  let B := T.stratumWeightedAdjoint S r levelEquiv
  have hpair := T.stratumWeightedAdjoint_pairing S r levelEquiv
    (G (G (B xi))) xi
  change T.terminalSpacing ^ d *
      inner ℝ (T.stratumAverage S r levelEquiv (G (G (B xi)))) xi =
    spacing ^ d * inner ℝ (G (G (B xi))) (B xi) at hpair
  change T.terminalSpacing ^ d *
      inner ℝ xi (T.stratumAverage S r levelEquiv (G (G (B xi)))) =
    spacing ^ d * ‖G (B xi)‖ ^ 2
  calc
    T.terminalSpacing ^ d *
        inner ℝ xi (T.stratumAverage S r levelEquiv (G (G (B xi)))) =
      T.terminalSpacing ^ d *
        inner ℝ (T.stratumAverage S r levelEquiv (G (G (B xi)))) xi := by
          rw [real_inner_comm]
    _ = spacing ^ d * inner ℝ (G (G (B xi))) (B xi) := hpair
    _ = spacing ^ d * inner ℝ (B xi) (G (G (B xi))) := by
          rw [real_inner_comm]
    _ = spacing ^ d * inner ℝ (G (B xi)) (G (B xi)) := by
          congr 1
          exact (hG (B xi) (G (B xi))).symm
    _ = spacing ^ d * ‖G (B xi)‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]

/-- A precision upper bound now gives stratum covariance coercivity with no
free lower-bound or surjectivity hypothesis. -/
theorem isCoerciveCLM_stratumCoarseCovarianceMiddle
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n)
    (levelEquiv : T.TerminalSpace.carrier ≃ₗᵢ[ℝ]
      CMP99SourceScaledStratification.ScaleField
        (ScaleSite := ScaleSite) g r)
    (A : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    {c Lambda : ℝ}
    (hspacing : 0 < spacing) (hterminal : 0 < T.terminalSpacing)
    (hc : 0 < c) (hLambdaPos : 0 < Lambda)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric)
    (hLambda : ‖A‖ ≤ Lambda) :
    IsCoerciveCLM
      (T.stratumCoarseCovarianceMiddle S r levelEquiv
        (covarianceOfIsCoerciveCLM A hc hA)) (Lambda ^ 2)⁻¹ := by
  intro xi
  let G := covarianceOfIsCoerciveCLM A hc hA
  let B := T.stratumWeightedAdjoint S r levelEquiv
  have hGsymm : G.IsSymmetric :=
    covarianceOfIsCoerciveCLM_isSymmetric A hc hA hSymm
  have hmiddle := T.weighted_inner_stratumCoarseCovarianceMiddle
    S r levelEquiv G hGsymm xi
  have hinverse := norm_le_mul_norm_covarianceOfIsCoerciveCLM
    A hc hA hLambda (B xi)
  have hsquare : ‖B xi‖ ^ 2 ≤ Lambda ^ 2 * ‖G (B xi)‖ ^ 2 := by
    nlinarith [norm_nonneg (B xi), norm_nonneg (G (B xi))]
  have hspacingPow : 0 < spacing ^ d := pow_pos hspacing d
  have hterminalPow : 0 < T.terminalSpacing ^ d :=
    pow_pos hterminal d
  have hscaled :
      T.terminalSpacing ^ d * ‖xi‖ ^ 2 ≤
        T.terminalSpacing ^ d *
          (inner ℝ xi
            (T.stratumCoarseCovarianceMiddle S r levelEquiv G xi) *
              Lambda ^ 2) := by
    calc
      T.terminalSpacing ^ d * ‖xi‖ ^ 2 =
          spacing ^ d * ‖B xi‖ ^ 2 :=
        (T.stratumWeightedAdjoint_spacingNormSq S r levelEquiv xi).symm
      _ ≤ spacing ^ d * (Lambda ^ 2 * ‖G (B xi)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsquare hspacingPow.le
      _ = T.terminalSpacing ^ d *
          (inner ℝ xi
            (T.stratumCoarseCovarianceMiddle S r levelEquiv G xi) *
              Lambda ^ 2) := by
        calc
          spacing ^ d * (Lambda ^ 2 * ‖G (B xi)‖ ^ 2) =
              Lambda ^ 2 * (spacing ^ d * ‖G (B xi)‖ ^ 2) := by ring
          _ = Lambda ^ 2 *
              (T.terminalSpacing ^ d * inner ℝ xi
                (T.stratumCoarseCovarianceMiddle S r levelEquiv G xi)) := by
                rw [← hmiddle]
          _ = T.terminalSpacing ^ d *
              (inner ℝ xi
                (T.stratumCoarseCovarianceMiddle S r levelEquiv G xi) *
                  Lambda ^ 2) := by ring
  have hbase : ‖xi‖ ^ 2 ≤
      inner ℝ xi
        (T.stratumCoarseCovarianceMiddle S r levelEquiv G xi) *
          Lambda ^ 2 := by
    nlinarith [hscaled]
  change (Lambda ^ 2)⁻¹ * ‖xi‖ ^ 2 ≤
    inner ℝ xi (T.stratumCoarseCovarianceMiddle S r levelEquiv G xi)
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (sq_pos_of_pos hLambdaPos)).2 (by
    simpa [mul_comm] using hbase)

end CMP99SourceWeightedRegionalTower

end

end YangMills.RG
