/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivativeBound
import YangMills.RG.BalabanCMP102Eq80JointPotentialSourceJetBound

/-!
# Source-generated equation-(80) bound for one physical domain coefficient

This module replaces every literal outer equation-(80) joint jet in the
finite Faà di Bruno domain sum by the majorant generated from the four source
terms.  The remainder budgets are imposed at the actual weakened-covariance
interpolation point and only through the maximal required order `n + 2`.

No hypothesis bounds the complete equation-(80) jet or a domain Hessian.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- The physical Faà di Bruno majorant after replacing each outer joint jet
by the four-term source-generated majorant at its actual order and point. -/
noncomputable def
    cmp102Eq80SourcePi4FaaDiBrunoSourceJetSecondFieldDerivativeMajorant
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (Ahead rho rate Rweak C Rjet : ℝ)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q))) : ℝ :=
  ∑ partition : OrderedFinpartition n,
    ∑ _choice ∈
        (Finset.univ :
          Finset (CMP102Eq80FaaDiBrunoDomainChoice
            (Q := Q) partition)).filter
          (fun choice =>
            cmp102Eq80SourcePi4AnchoredDomainUnion anchor
              Finset.univ choice = W),
      cmp102Eq80JointPotentialSourceJetMajorant D D₃ Δπ J
          (partition.length + 2)
          (cmp116FiniteMultiaffineInterpolation
              (fun u =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK u ∅)
              vertexBase L sigma,
            A) C Rjet *
        (cmp102Eq80SourcePi4DomainDirectionMajorant
          Nc Δ Ahead rho rate Rweak) ^ partition.length

set_option maxHeartbeats 4000000 in
/-- The complete second-field derivative of one physical source-domain
coefficient is bounded by source-generated component jets.  The only
remainder inputs are derivatives of `V₀` and the displayed inner-map budget
at the literal weakened-covariance interpolation point. -/
theorem
    norm_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt_le_sourceJet
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (W : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖(sigma d : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (C Rjet : ℝ)
    (hC : ∀ i, i ≤ n + 2 →
      ‖iteratedFDeriv ℝ i V₀
        (cmp102Eq80JointRemainderInner D
          (cmp116FiniteMultiaffineInterpolation
              (fun u =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK u ∅)
              vertexBase L sigma,
            A))‖ ≤ C)
    (hRjet : ∀ i, 1 ≤ i → i ≤ n + 2 →
      ‖iteratedFDeriv ℝ i
          (fun q :
              PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
            q.2)
          (cmp116FiniteMultiaffineInterpolation
              (fun u =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK u ∅)
              vertexBase L sigma,
            A)‖ +
        cmp102Eq80JointEvaluationJetMajorant D i
          (cmp116FiniteMultiaffineInterpolation
              (fun u =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK u ∅)
              vertexBase L sigma,
            A) ≤ Rjet ^ i) :
    ‖cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates W‖ ≤
      cmp102Eq80SourcePi4FaaDiBrunoSourceJetSecondFieldDerivativeMajorant
        (R := R) (Δ := Δ) (n := n)
        anchor K hc hmass hK D D₃ Δπ J A
        Ahead rho rate Rweak C Rjet vertexBase sigma L W := by
  classical
  have hstep :
      cmp102Eq80SourcePi4FaaDiBrunoSecondFieldDerivativeJetMajorant
          (R := R) (Δ := Δ) (n := n)
          anchor K hc hmass hK D D₃ V₀ Δπ J A
          Ahead rho rate Rweak vertexBase sigma L W ≤
        cmp102Eq80SourcePi4FaaDiBrunoSourceJetSecondFieldDerivativeMajorant
          (R := R) (Δ := Δ) (n := n)
          anchor K hc hmass hK D D₃ Δπ J A
          Ahead rho rate Rweak C Rjet vertexBase sigma L W := by
    unfold
      cmp102Eq80SourcePi4FaaDiBrunoSecondFieldDerivativeJetMajorant
    unfold
      cmp102Eq80SourcePi4FaaDiBrunoSourceJetSecondFieldDerivativeMajorant
    apply Finset.sum_le_sum
    intro partition _hpartition
    apply Finset.sum_le_sum
    intro choice _hchoice
    have hlen : partition.length + 2 ≤ n + 2 :=
      Nat.add_le_add_right (OrderedFinpartition.length_le partition) 2
    have hjet :=
      norm_iteratedFDeriv_cmp102Eq80JointPotential_le_sourceJetMajorant
        D D₃ V₀ Δπ J hD hD₃ hV₀ (partition.length + 2)
        (cmp116FiniteMultiaffineInterpolation
            (fun u =>
              cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                (R := R) anchor K hc hmass hK u ∅)
            vertexBase L sigma,
          A) C Rjet
        (fun i hi => hC i (hi.trans hlen))
        (fun i hi₁ hi => hRjet i hi₁ (hi.trans hlen))
    exact mul_le_mul_of_nonneg_right hjet
      (pow_nonneg
        (cmp102Eq80SourcePi4DomainDirectionMajorant_nonneg
          hAhead hrho hRweak hgeom hsmall) _)
  exact le_trans
    (norm_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt_le
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      vertexBase sigma L coordinates W hRweak hcap hsmall)
    hstep

end

end YangMills.RG
