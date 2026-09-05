/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCSecondFieldDerivative

/-!
# Joint continuity of the second derivative through the FTC tree

The proof follows the literal connected-domain recursion.  A globally
clamped weakening path preserves the source contour certificate, while on
`[0,1]` it agrees exactly with the updates in the original interval
integrals.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

set_option maxHeartbeats 128000000 in
/-- The recursive second derivative is jointly continuous when the field
and every weakening coordinate vary continuously. -/
theorem
    continuous_cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative_comp
    {M Q Nc R Δ : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T] [FirstCountableTopology T] [LocallyCompactSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
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
    (A : T → PhysicalField M Q Nc) (hA : Continuous A)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (n : ℕ) (coordinates : Fin n → FinBox 4 (2 * Q))
    (sigma : T → FinBox 4 (2 * Q) → ℝ)
    (remaining : List (FinBox 4 (2 * Q)))
    (hsigma : ∀ d, Continuous fun x => sigma x d)
    (hRweak : 1 ≤ Rweak)
    (hsigmaRegion :
      ∀ x, CMP116RealPhysicalContourRegion Rweak (sigma x))
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    Continuous fun x =>
      cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A x)
        vertexBase vertexCoordinates W n coordinates
        (sigma x) remaining := by
  classical
  induction remaining generalizing T n sigma A with
  | nil =>
      by_cases hn : n = 0
      · simpa [
          cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative,
          hn] using
          (continuous_const :
            Continuous (fun _ : T =>
              (0 : PhysicalField M Q Nc →L[ℝ]
                PhysicalField M Q Nc →L[ℝ] ℝ)))
      · simpa [
          cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative,
          hn] using
          continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt_comp
            anchor K hc hmass hK D D₃ V₀ Δπ J
            hAhead hrho hrate Cert htri hrange hΔ hΔ1
            A hA vertexBase sigma hsigma vertexCoordinates coordinates W
            hRweak (fun x d => (hsigmaRegion x).2 d) hsmall
            hD hD₃ hV₀
  | cons d tail ih =>
      let sigmaZero : T → FinBox 4 (2 * Q) → ℝ :=
        fun x => Function.update (sigma x) d 0
      have hsigmaZero (e : FinBox 4 (2 * Q)) :
          Continuous fun x => sigmaZero x e := by
        by_cases hed : e = d
        · subst e
          simpa [sigmaZero] using
            (continuous_const : Continuous (fun _ : T => (0 : ℝ)))
        · simpa [sigmaZero, Function.update_of_ne hed] using hsigma e
      have hsigmaZeroRegion (x : T) :
          CMP116RealPhysicalContourRegion Rweak (sigmaZero x) :=
        cmp116RealPhysicalContourRegion_update_uIcc
          Rweak hRweak (sigma x) d 0 (hsigmaRegion x) (by simp)
      have hbase :
          Continuous fun x =>
            cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A x)
              vertexBase vertexCoordinates W n coordinates
              (sigmaZero x) tail :=
        ih A hA n coordinates sigmaZero hsigmaZero
          hsigmaZeroRegion
      let sigmaFiber :
          (T × ℝ) → FinBox 4 (2 * Q) → ℝ :=
        fun p =>
          cmp116ClampedRealWeakeningCoordinatePath (sigma p.1) d p.2
      have hsigmaFiber (e : FinBox 4 (2 * Q)) :
          Continuous fun p : T × ℝ => sigmaFiber p e := by
        by_cases hed : e = d
        · subst e
          simpa [sigmaFiber,
            cmp116ClampedRealWeakeningCoordinatePath] using
            continuous_cmp116ClampUnit.comp continuous_snd
        · have hde : d ≠ e := Ne.symm hed
          simpa [sigmaFiber,
            cmp116ClampedRealWeakeningCoordinatePath,
            Function.update, hed, hde] using
            (hsigma e).comp continuous_fst
      have hsigmaFiberRegion (p : T × ℝ) :
          CMP116RealPhysicalContourRegion Rweak (sigmaFiber p) :=
        cmp116ClampedRealWeakeningCoordinatePath_mem_contourRegion
          Rweak hRweak (sigma p.1) (hsigmaRegion p.1) d p.2
      have hfiber :
          Continuous fun p : T × ℝ =>
            cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A p.1)
              vertexBase vertexCoordinates W (n + 1)
              (Fin.cons d coordinates) (sigmaFiber p) tail :=
        ih (fun p : T × ℝ => A p.1) (hA.comp continuous_fst)
          (n + 1) (Fin.cons d coordinates)
          sigmaFiber hsigmaFiber hsigmaFiberRegion
      have hintegralClamped :
          Continuous fun x =>
            ∫ t in Set.uIcc (0 : ℝ) 1,
              cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A x)
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber (x, t)) tail :=
        continuous_parametric_integral_of_continuous
          hfiber isCompact_uIcc
      have hintegralEq (x : T) :
          (∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A x)
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates)
                (Function.update (sigma x) d t) tail) =
            ∫ t in Set.uIcc (0 : ℝ) 1,
              cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A x)
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber (x, t)) tail := by
        rw [intervalIntegral.integral_of_le zero_le_one]
        rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
        simp only [Set.uIcc_of_le zero_le_one]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro t ht
        have heq :
            sigmaFiber (x, t) = Function.update (sigma x) d t :=
          cmp116ClampedRealWeakeningCoordinatePath_eq_update
            (sigma x) d ht
        exact congrArg
          (fun u =>
            cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A x)
              vertexBase vertexCoordinates W (n + 1)
              (Fin.cons d coordinates) u tail)
          heq.symm
      have hintegral :
          Continuous fun x =>
            ∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A x)
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates)
                (Function.update (sigma x) d t) tail := by
        apply hintegralClamped.congr
        intro x
        exact (hintegralEq x).symm
      simpa [
        cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative,
        sigmaZero] using hbase.add hintegral

end

end YangMills.RG
