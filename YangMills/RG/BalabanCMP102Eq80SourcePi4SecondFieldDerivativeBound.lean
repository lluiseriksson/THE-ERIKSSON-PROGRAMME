/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivative
import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredOperatorBound

/-!
# Quantitative physical-direction bounds for equation-(80) second derivatives

The source-domain second derivative is a mixed jet: the first variables
differentiate the weakened propagator and the final two variables
differentiate the physical field.  This file keeps those roles separate.

First, the norm of the extracted bilinear field derivative is bounded by the
norm of the literal joint iterated derivative times the product of the
propagator-direction norms.  The source-specific corollary then discharges
every propagator-direction norm with the already proved, volume-uniform
carrier-anchored operator bound.

Honest scope: the remaining outer-jet norm is the iterated derivative of the
literal four-term equation-(80) potential.  It is displayed, not renamed as a
domain-Hessian hypothesis.  Bounding that source jet from the component
derivatives of `D`, `D₃`, and `V₀` is the next analytic step toward (1.43).
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

/-- Extracting the final two physical-field variables from a joint
`(n + 2)`-jet costs exactly the product of the first `n` propagator-direction
norms.  No factorial or ambient-dimension factor is introduced. -/
theorem norm_cmp102PartialPropagatorJetSecondFieldDerivative_le
    {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) :
    ‖cmp102PartialPropagatorJetSecondFieldDerivative F n h v x‖ ≤
      ‖iteratedFDeriv ℝ (n + 2) F (h, x)‖ * ∏ i, ‖v i‖ := by
  let C :=
    ‖iteratedFDeriv ℝ (n + 2) F (h, x)‖ * ∏ i, ‖v i‖
  have hC : 0 ≤ C :=
    mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hC (norm_nonneg a))
  intro b
  rw [cmp102PartialPropagatorJetSecondFieldDerivative_apply]
  let directions : Fin (n + 2) → H × E :=
    Fin.snoc (Fin.snoc (fun i => (v i, 0)) (0, b)) (0, a)
  have hprod :
      ∏ i, ‖directions i‖ = (∏ i, ‖v i‖) * ‖b‖ * ‖a‖ := by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp [directions]
  calc
    ‖iteratedFDeriv ℝ (n + 2) F (h, x) directions‖ ≤
        ‖iteratedFDeriv ℝ (n + 2) F (h, x)‖ *
          ∏ i, ‖directions i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = (C * ‖a‖) * ‖b‖ := by
      rw [hprod]
      ring

/-- The common physical majorant for every carrier-anchored propagator
direction in one source-domain coefficient. -/
noncomputable def cmp102Eq80SourcePi4DomainDirectionMajorant
    (Nc Δ : ℕ) (Ahead rho rate Rweak : ℝ) : ℝ :=
  (cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
    (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹) *
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)

/-- Under the same smallness and geometric hypotheses used by the physical
operator estimate, the displayed direction majorant is nonnegative. -/
theorem cmp102Eq80SourcePi4DomainDirectionMajorant_nonneg
    {Nc Δ : ℕ} {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho)
    (hRweak : 1 ≤ Rweak)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    0 ≤ cmp102Eq80SourcePi4DomainDirectionMajorant
      Nc Δ Ahead rho rate Rweak := by
  have hRweak0 : 0 ≤ Rweak := le_trans (by norm_num) hRweak
  have hprefactor :
      0 ≤ cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak := by
    unfold cmp116SourcePi4MixedDerivativeDomainPrefactor
    positivity
  have hratio0 :
      0 ≤ cmp116SourcePi4ComplexContourRatio Δ rho Rweak := by
    unfold cmp116SourcePi4ComplexContourRatio
    positivity
  have hratio_lt :
      cmp116SourcePi4ComplexContourRatio Δ rho Rweak < 1 := by
    exact lt_of_le_of_lt
      (le_trans (le_abs_self _)
        (by simp [Real.norm_eq_abs]))
      hsmall
  unfold cmp102Eq80SourcePi4DomainDirectionMajorant
  exact mul_nonneg
    (mul_nonneg hprefactor
      (inv_nonneg.mpr (sub_nonneg.mpr hratio_lt.le)))
    (mul_nonneg (Nat.cast_nonneg _)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom))

/-- One source-domain choice is bounded by the literal outer equation-(80)
joint jet times the physical direction majorant to the exact partition
length. -/
theorem
    norm_cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt_le
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
    (partition : OrderedFinpartition n)
    (choice : CMP102Eq80FaaDiBrunoDomainChoice
      (Q := Q) partition)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖(sigma d : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ‖cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates partition choice‖ ≤
      ‖iteratedFDeriv ℝ (partition.length + 2)
          (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
            cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
          (cmp116FiniteMultiaffineInterpolation
              (fun u =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK u ∅)
              vertexBase L sigma,
            A)‖ *
        (cmp102Eq80SourcePi4DomainDirectionMajorant
          Nc Δ Ahead rho rate Rweak) ^ partition.length := by
  let F :=
    fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  let H₀ :=
    cmp116FiniteMultiaffineInterpolation
      (fun u =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK u ∅)
      vertexBase L sigma
  let directions :=
    fun block =>
      cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
        (R := R) anchor K hc hmass hK sigma
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
        (choice block)
  let B :=
    cmp102Eq80SourcePi4DomainDirectionMajorant
      Nc Δ Ahead rho rate Rweak
  have hB0 : 0 ≤ B :=
    cmp102Eq80SourcePi4DomainDirectionMajorant_nonneg
      hAhead hrho hRweak hgeom hsmall
  have hdirection (block : Fin partition.length) :
      ‖directions block‖ ≤ B := by
    simpa [directions, B,
      cmp102Eq80SourcePi4DomainDirectionMajorant] using
      (norm_cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_le
        (R := R) anchor K hc hmass hK hAhead hrho hrate hgeom
        Cert htri hrange hΔ hΔ1 sigma hRweak hcap
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
        (choice block) hsmall)
  have hprod :
      ∏ block, ‖directions block‖ ≤ B ^ partition.length := by
    calc
      ∏ block, ‖directions block‖ ≤
          ∏ _block : Fin partition.length, B := by
        apply Finset.prod_le_prod
        · intro block _hblock
          exact norm_nonneg _
        · intro block _hblock
          exact hdirection block
      _ = B ^ partition.length := by simp
  have hjet :=
    norm_cmp102PartialPropagatorJetSecondFieldDerivative_le
      F partition.length H₀ directions A
  have houter :
      0 ≤ ‖iteratedFDeriv ℝ (partition.length + 2) F (H₀, A)‖ :=
    norm_nonneg
      (iteratedFDeriv ℝ (partition.length + 2) F (H₀, A))
  exact le_trans hjet
    (mul_le_mul_of_nonneg_left hprod houter)

/-- The literal finite Faà di Bruno majorant remaining after all physical
propagator directions have been bounded.  It retains the actual filtered
choice count and the actual order of the outer equation-(80) joint jet. -/
noncomputable def
    cmp102Eq80SourcePi4FaaDiBrunoSecondFieldDerivativeJetMajorant
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
    (Ahead rho rate Rweak : ℝ)
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
      ‖iteratedFDeriv ℝ (partition.length + 2)
          (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
            cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
          (cmp116FiniteMultiaffineInterpolation
              (fun u =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK u ∅)
              vertexBase L sigma,
            A)‖ *
        (cmp102Eq80SourcePi4DomainDirectionMajorant
          Nc Δ Ahead rho rate Rweak) ^ partition.length

set_option maxHeartbeats 4000000
/-- The complete source-domain coefficient, after both finite Faà di Bruno
sums, is bounded by the explicit outer-jet majorant.  Thus no domain-level
Hessian bound remains as an input: all domain directions are produced and
bounded internally. -/
theorem
    norm_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt_le
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
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ‖cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates W‖ ≤
      cmp102Eq80SourcePi4FaaDiBrunoSecondFieldDerivativeJetMajorant
        (R := R) (Δ := Δ) (n := n)
        anchor K hc hmass hK D D₃ V₀ Δπ J A
        Ahead rho rate Rweak vertexBase sigma L W := by
  classical
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoSecondFieldDerivativeJetMajorant
  calc
    ‖∑ partition : OrderedFinpartition n,
        ∑ choice ∈
            (Finset.univ :
              Finset (CMP102Eq80FaaDiBrunoDomainChoice
                (Q := Q) partition)).filter
              (fun choice =>
                cmp102Eq80SourcePi4AnchoredDomainUnion anchor
                  Finset.univ choice = W),
          cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase sigma L coordinates partition choice‖ ≤
        ∑ partition : OrderedFinpartition n,
          ‖∑ choice ∈
              (Finset.univ :
                Finset (CMP102Eq80FaaDiBrunoDomainChoice
                  (Q := Q) partition)).filter
                (fun choice =>
                  cmp102Eq80SourcePi4AnchoredDomainUnion anchor
                    Finset.univ choice = W),
            cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase sigma L coordinates partition choice‖ :=
      by
        simpa using
          (norm_sum_le
            (Finset.univ : Finset (OrderedFinpartition n))
            (fun partition =>
              ∑ choice ∈
                  (Finset.univ :
                    Finset (CMP102Eq80FaaDiBrunoDomainChoice
                      (Q := Q) partition)).filter
                    (fun choice =>
                      cmp102Eq80SourcePi4AnchoredDomainUnion anchor
                        Finset.univ choice = W),
                cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
                  (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                  vertexBase sigma L coordinates partition choice))
    _ ≤
        ∑ partition : OrderedFinpartition n,
          ∑ choice ∈
              (Finset.univ :
                Finset (CMP102Eq80FaaDiBrunoDomainChoice
                  (Q := Q) partition)).filter
                (fun choice =>
                  cmp102Eq80SourcePi4AnchoredDomainUnion anchor
                    Finset.univ choice = W),
            ‖cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase sigma L coordinates partition choice‖ := by
      apply Finset.sum_le_sum
      intro partition _hpartition
      simpa using
        (norm_sum_le
          ((Finset.univ :
            Finset (CMP102Eq80FaaDiBrunoDomainChoice
              (Q := Q) partition)).filter
            (fun choice =>
              cmp102Eq80SourcePi4AnchoredDomainUnion anchor
                Finset.univ choice = W))
          (fun choice =>
            cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase sigma L coordinates partition choice))
    _ ≤
        ∑ partition : OrderedFinpartition n,
          ∑ _choice ∈
              (Finset.univ :
                Finset (CMP102Eq80FaaDiBrunoDomainChoice
                  (Q := Q) partition)).filter
                (fun choice =>
                  cmp102Eq80SourcePi4AnchoredDomainUnion anchor
                    Finset.univ choice = W),
            ‖iteratedFDeriv ℝ (partition.length + 2)
                (fun p :
                    PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
                  cmp102Eq80GlobalPotential
                    D D₃ V₀ p.1 Δπ J p.2)
                (cmp116FiniteMultiaffineInterpolation
                    (fun u =>
                      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                        (R := R) anchor K hc hmass hK u ∅)
                    vertexBase L sigma,
                  A)‖ *
              (cmp102Eq80SourcePi4DomainDirectionMajorant
                Nc Δ Ahead rho rate Rweak) ^ partition.length := by
      apply Finset.sum_le_sum
      intro partition _hpartition
      apply Finset.sum_le_sum
      intro choice hchoice
      exact
        norm_cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt_le
          anchor K hc hmass hK D D₃ V₀ Δπ J A
          hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
          vertexBase sigma L coordinates partition choice
          hRweak hcap hsmall

set_option maxHeartbeats 200000

end

end YangMills.RG
