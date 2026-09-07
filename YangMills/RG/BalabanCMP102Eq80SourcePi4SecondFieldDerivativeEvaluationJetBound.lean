/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivativeSourceJetBound

/-!
# Eliminate the field-projection jet from the equation-(80) domain bound

The remainder inner map is the difference between the field projection and
the evaluated physical map.  This module evaluates the projection jet
exactly: it has norm at most one in order one and vanishes in every higher
positive order.  The physical domain theorem can consequently be stated
using only a bound for the source-generated evaluation jet of `D`.
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

/-- Exact scalar majorant for the positive-order jets of the second
projection. -/
def cmp102Eq80JointFieldProjectionJetMajorant (i : ℕ) : ℝ :=
  if i = 1 then 1 else 0

/-- The second projection contributes only its first derivative. -/
theorem norm_iteratedFDeriv_jointFieldProjection_le
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : ℕ) (hi : 1 ≤ i) (p : E × F) :
    ‖iteratedFDeriv ℝ i (fun q : E × F => q.2) p‖ ≤
      cmp102Eq80JointFieldProjectionJetMajorant i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  cases k with
  | zero =>
      unfold cmp102Eq80JointFieldProjectionJetMajorant
      simpa [norm_iteratedFDeriv_one, fderiv_snd] using
        (ContinuousLinearMap.norm_snd_le ℝ E F)
  | succ k =>
      unfold cmp102Eq80JointFieldProjectionJetMajorant
      have hderiv :
          (fun y : E × F =>
            fderiv ℝ (fun q : E × F => q.2) y) =
            fun _ => ContinuousLinearMap.snd ℝ E F := by
        funext y
        exact fderiv_snd
      rw [show 1 + (k + 1) = (k + 1) + 1 by omega]
      rw [iteratedFDeriv_succ_eq_comp_right, hderiv]
      have hzero :
          (iteratedFDeriv ℝ (k + 1)
            (fun _ : E × F => ContinuousLinearMap.snd ℝ E F)) = 0 :=
        iteratedFDeriv_const_of_ne (by omega) _
      rw [hzero]
      have hne : k + 1 + 1 ≠ 1 := by omega
      rw [if_neg hne]
      simp only [Function.comp_apply, Pi.zero_apply]
      have hcurryZero :
          (continuousMultilinearCurryRightEquiv'
            ℝ (k + 1) (E × F) F).symm 0 = 0 :=
        (continuousMultilinearCurryRightEquiv'
          ℝ (k + 1) (E × F) F).symm.map_zero
      rw [hcurryZero, norm_zero]

set_option maxHeartbeats 4000000 in
/-- Source-generated physical domain bound with the linear field projection
discharged internally.  The radius premise now contains only the explicit
evaluation-jet majorant of `D`, plus the exact projection contribution
`1` in order one and `0` thereafter. -/
theorem
    norm_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt_le_sourceEvaluationJet
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
    (hEvaluation : ∀ i, 1 ≤ i → i ≤ n + 2 →
      cmp102Eq80JointFieldProjectionJetMajorant i +
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
  apply
    norm_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt_le_sourceJet
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hD hD₃ hV₀ hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      vertexBase sigma L coordinates W hRweak hcap hsmall C Rjet hC
  intro i hi hiMax
  calc
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
            A) ≤
      cmp102Eq80JointFieldProjectionJetMajorant i +
        cmp102Eq80JointEvaluationJetMajorant D i
          (cmp116FiniteMultiaffineInterpolation
              (fun u =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK u ∅)
              vertexBase L sigma,
            A) := by
      exact add_le_add
        (norm_iteratedFDeriv_jointFieldProjection_le
          (E := PhysicalEndomorphism M Q Nc)
          (F := PhysicalField M Q Nc) i hi
          (cmp116FiniteMultiaffineInterpolation
              (fun u =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK u ∅)
              vertexBase L sigma,
            A))
        (le_refl _)
    _ ≤ Rjet ^ i := hEvaluation i hi hiMax

end

end YangMills.RG
