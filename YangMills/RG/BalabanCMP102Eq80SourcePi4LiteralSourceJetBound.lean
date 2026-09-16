/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80JointEvaluationSourceJetBound

/-!
# Literal source-jet terminal bound for one equation-(80) domain

The preceding physical domain theorem still exposes the auxiliary joint
evaluation jet used while differentiating the remainder composition.  This
file consumes the exact projection-jet calculation and the source-only
evaluation estimate.  Its terminal radius premise contains only the literal
derivatives of the physical correction `D`.

No bound for the complete equation-(80) jet, the joint evaluation map, or a
domain Hessian is assumed.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev LiteralPhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev LiteralPhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  LiteralPhysicalField M Q Nc →L[ℝ] LiteralPhysicalField M Q Nc

/-- Source-faithful terminal form of the physical domain estimate.  The
evaluation-radius premise now mentions only the exact projection jet and the
literal derivatives of the source correction `D`; the auxiliary joint
evaluation majorant is generated internally. -/
theorem
    norm_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt_le_literalSourceJets
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : LiteralPhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : LiteralPhysicalField M Q Nc → LiteralPhysicalField M Q Nc)
    (V₀ : LiteralPhysicalField M Q Nc → ℝ)
    (Δπ : LiteralPhysicalEndomorphism M Q Nc)
    (J A : LiteralPhysicalField M Q Nc)
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
      cmp102Eq80JointFieldProjectionJetMajorant i +
        cmp102Eq80JointEvaluationSourceJetMajorant D i
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
  apply
    norm_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt_le_sourceJet
      anchor K hc hmass hK D D₃ V₀ Δπ J A hD hD₃ hV₀
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      vertexBase sigma L coordinates W hRweak hcap hsmall C Rjet hC
  intro i hi₁ hi₂
  let p :
      LiteralPhysicalEndomorphism M Q Nc × LiteralPhysicalField M Q Nc :=
    (cmp116FiniteMultiaffineInterpolation
        (fun u =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK u ∅)
        vertexBase L sigma,
      A)
  have heval :
      cmp102Eq80JointFieldProjectionJetMajorant i +
          cmp102Eq80JointEvaluationJetMajorant D i p ≤
        Rjet ^ i :=
    cmp102Eq80JointRemainderRadius_of_sourceEvaluation
      D hD i p Rjet (hRjet i hi₁ hi₂)
  have hprojection :
      ‖iteratedFDeriv ℝ i
          (fun q :
              LiteralPhysicalEndomorphism M Q Nc ×
                LiteralPhysicalField M Q Nc =>
            q.2) p‖ ≤
        cmp102Eq80JointFieldProjectionJetMajorant i :=
    norm_iteratedFDeriv_jointFieldProjection_le i hi₁ p
  exact
    (add_le_add hprojection le_rfl).trans heval

end

end YangMills.RG
