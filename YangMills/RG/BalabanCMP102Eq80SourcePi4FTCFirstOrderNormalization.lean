/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCFieldDerivativeContinuity

/-!
# First-order normalization of the complete equation-(80) FTC activity

The explicit derivative constructed from the next joint propagator/field
jet is the actual Fréchet derivative of every node in the literal FTC
tree.  At an integral node we use joint continuity of the recursive
activity and derivative to generate the compact dominated bound
internally, then apply the parametric interval theorem.

The globally clamped weakening path preserves the physical contour
certificate.  On the integration interval it agrees exactly with the
literal `Function.update`, so the resulting theorem is about the original
source activity rather than an auxiliary extension.
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
/-- At every intermediate node, the explicit recursive field derivative is
the actual Fréchet derivative of the connected-domain activity. -/
theorem cmp102Eq80SourcePi4FTCConnectedDomainActivity_hasFDerivAt
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
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (sigma : FinBox 4 (2 * Q) → ℝ)
    (remaining : List (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hsigma :
      CMP116RealPhysicalContourRegion Rweak sigma)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    HasFDerivAt
      (fun x =>
        cmp102Eq80SourcePi4FTCConnectedDomainActivity
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
          vertexBase vertexCoordinates W n coordinates sigma remaining)
      (cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates W n coordinates sigma remaining)
      A := by
  classical
  induction remaining generalizing n coordinates sigma A with
  | nil =>
      by_cases hn : n = 0
      · simpa [cmp102Eq80SourcePi4FTCConnectedDomainActivity,
          cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative, hn] using
          (hasFDerivAt_const (x := A) (c := (0 : ℝ)))
      · simpa [cmp102Eq80SourcePi4FTCConnectedDomainActivity,
          cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative, hn] using
          cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_hasFDerivAt_explicit
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase sigma vertexCoordinates coordinates W
            hD hD₃ hV₀
  | cons d tail ih =>
      have hsigmaZero :
          CMP116RealPhysicalContourRegion Rweak
            (Function.update sigma d 0) :=
        cmp116RealPhysicalContourRegion_update_uIcc
          Rweak hRweak sigma d 0 hsigma (by simp)
      have hbase :=
        ih (A := A) (n := n) (coordinates := coordinates)
          (sigma := Function.update sigma d 0) hsigmaZero
      let sigmaFiber :
          (PhysicalField M Q Nc × ℝ) →
            FinBox 4 (2 * Q) → ℝ :=
        fun p =>
          cmp116ClampedRealWeakeningCoordinatePath sigma d p.2
      have hsigmaFiber (e : FinBox 4 (2 * Q)) :
          Continuous fun p : PhysicalField M Q Nc × ℝ =>
            sigmaFiber p e := by
        by_cases hed : e = d
        · subst e
          simpa [sigmaFiber,
            cmp116ClampedRealWeakeningCoordinatePath] using
            continuous_cmp116ClampUnit.comp continuous_snd
        · have hde : d ≠ e := Ne.symm hed
          simpa [sigmaFiber,
            cmp116ClampedRealWeakeningCoordinatePath,
            Function.update, hed, hde] using
            (continuous_const :
              Continuous fun _ : PhysicalField M Q Nc × ℝ => sigma e)
      have hsigmaFiberRegion
          (p : PhysicalField M Q Nc × ℝ) :
          CMP116RealPhysicalContourRegion Rweak (sigmaFiber p) :=
        cmp116ClampedRealWeakeningCoordinatePath_mem_contourRegion
          Rweak hRweak sigma hsigma d p.2
      have hpair :
          Continuous fun p : PhysicalField M Q Nc × ℝ =>
            (cmp102Eq80SourcePi4FTCConnectedDomainActivity
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J p.1
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber p) tail,
              cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J p.1
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber p) tail) :=
        continuous_cmp102Eq80SourcePi4FTCConnectedDomainActivity_and_fieldDerivative_comp
          anchor K hc hmass hK D D₃ V₀ Δπ J
          hAhead hrho hrate Cert htri hrange hΔ hΔ1
          (fun p : PhysicalField M Q Nc × ℝ => p.1) continuous_fst
          vertexBase vertexCoordinates W (n + 1)
          (Fin.cons d coordinates) sigmaFiber tail hsigmaFiber
          hRweak hsigmaFiberRegion hsmall hD hD₃ hV₀
      have hintegralClamped :
          HasFDerivAt
            (fun x : PhysicalField M Q Nc =>
              ∫ t in (0 : ℝ)..1,
                cmp102Eq80SourcePi4FTCConnectedDomainActivity
                  (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
                  vertexBase vertexCoordinates W (n + 1)
                  (Fin.cons d coordinates) (sigmaFiber (x, t)) tail)
            (∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber (A, t)) tail)
            A := by
        apply
          hasFDerivAt_intervalIntegral_of_continuous_fieldDerivative
            (F := fun p : PhysicalField M Q Nc × ℝ =>
              cmp102Eq80SourcePi4FTCConnectedDomainActivity
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J p.1
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber p) tail)
            (F' := fun p : PhysicalField M Q Nc × ℝ =>
              cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J p.1
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber p) tail)
            A hpair.fst hpair.snd
        intro x t
        exact ih (A := x) (n := n + 1)
          (coordinates := Fin.cons d coordinates)
          (sigma := sigmaFiber (x, t))
          (hsigmaFiberRegion (x, t))
      have hfunEq :
          (fun x : PhysicalField M Q Nc =>
              ∫ t in (0 : ℝ)..1,
                cmp102Eq80SourcePi4FTCConnectedDomainActivity
                  (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
                  vertexBase vertexCoordinates W (n + 1)
                  (Fin.cons d coordinates)
                  (Function.update sigma d t) tail) =
            (fun x : PhysicalField M Q Nc =>
              ∫ t in (0 : ℝ)..1,
                cmp102Eq80SourcePi4FTCConnectedDomainActivity
                  (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
                  vertexBase vertexCoordinates W (n + 1)
                  (Fin.cons d coordinates) (sigmaFiber (x, t)) tail) := by
        funext x
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Set.uIcc_of_le zero_le_one] using ht
        have heq :
            sigmaFiber (x, t) = Function.update sigma d t :=
          cmp116ClampedRealWeakeningCoordinatePath_eq_update
            sigma d ht'
        exact congrArg
          (fun u =>
            cmp102Eq80SourcePi4FTCConnectedDomainActivity
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
              vertexBase vertexCoordinates W (n + 1)
              (Fin.cons d coordinates) u tail)
          heq.symm
      have hderivEq :
          (∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates)
                (Function.update sigma d t) tail) =
            ∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber (A, t)) tail := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Set.uIcc_of_le zero_le_one] using ht
        have heq :
            sigmaFiber (A, t) = Function.update sigma d t :=
          cmp116ClampedRealWeakeningCoordinatePath_eq_update
            sigma d ht'
        exact congrArg
          (fun u =>
            cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase vertexCoordinates W (n + 1)
              (Fin.cons d coordinates) u tail)
          heq.symm
      have hintegral :
          HasFDerivAt
            (fun x : PhysicalField M Q Nc =>
              ∫ t in (0 : ℝ)..1,
                cmp102Eq80SourcePi4FTCConnectedDomainActivity
                  (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
                  vertexBase vertexCoordinates W (n + 1)
                  (Fin.cons d coordinates)
                  (Function.update sigma d t) tail)
            (∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates)
                (Function.update sigma d t) tail)
            A := by
        rw [hfunEq, hderivEq]
        exact hintegralClamped
      simpa [cmp102Eq80SourcePi4FTCConnectedDomainActivity,
        cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative] using
        hbase.add hintegral

/-- The source-level connected-domain activity has zero physical-field
derivative at the origin.  The result is derived through the literal FTC
tree and contains no derivative/integral commutation premise. -/
theorem
    cmp102Eq80SourcePi4ConnectedDomainActivity_hasFDerivAt_zero_field
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
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
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hs : CMP116RealPhysicalContourRegion Rweak s)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0) :
    HasFDerivAt
      (fun x =>
        cmp102Eq80SourcePi4ConnectedDomainActivity
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
          vertexBase vertexCoordinates s L W)
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ)
      0 := by
  have hder :=
    cmp102Eq80SourcePi4FTCConnectedDomainActivity_hasFDerivAt
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      vertexBase vertexCoordinates W Fin.elim0 s L
      hRweak hs hsmall hD hD₃ hV₀
  have hzero :=
    cmp102Eq80SourcePi4ConnectedDomainFieldDerivative_zero_field
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      vertexBase vertexCoordinates s L W
      hD hD₃ hV₀ hD0 hD₃0 hD₃' hV₀'
  have hzero' :
      cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
          vertexBase vertexCoordinates W 0 Fin.elim0 s L = 0 := by
    simpa [cmp102Eq80SourcePi4ConnectedDomainFieldDerivative] using hzero
  rw [hzero'] at hder
  simpa [cmp102Eq80SourcePi4ConnectedDomainActivity,
    cmp102Eq80SourcePi4ConnectedDomainFieldDerivative] using hder

end

end YangMills.RG
