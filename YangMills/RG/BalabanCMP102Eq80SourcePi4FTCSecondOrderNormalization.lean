/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCSecondFieldDerivativeContinuity
import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCFirstOrderNormalization

/-!
# Second-order regularity of the complete equation-(80) FTC activity

The second derivative constructed from the next source joint jet is the
actual Fréchet derivative of the first-derivative tree.  Differentiation
under every weakening integral uses the Banach-valued parametric theorem,
with domination generated internally from compactness and joint
continuity.

The terminal theorem proves `ContDiff ℝ 2` for the literal connected
equation-(80) activity.  This is the regularity required by the radial
Taylor construction of the physical quadratic core.
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
/-- At every intermediate FTC node, the explicit second derivative is the
actual Fréchet derivative of the explicit first derivative. -/
theorem
    cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative_hasFDerivAt
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
        cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
          vertexBase vertexCoordinates W n coordinates sigma remaining)
      (cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates W n coordinates sigma remaining)
      A := by
  classical
  induction remaining generalizing n coordinates sigma A with
  | nil =>
      by_cases hn : n = 0
      · simpa [
          cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative,
          cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative,
          hn] using
          (hasFDerivAt_const (x := A)
            (c := (0 : PhysicalField M Q Nc →L[ℝ] ℝ)))
      · simpa [
          cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative,
          cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative,
          hn] using
          cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt_hasFDerivAt
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
      have hfirstPair :
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
      have hsecond :
          Continuous fun p : PhysicalField M Q Nc × ℝ =>
            cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J p.1
              vertexBase vertexCoordinates W (n + 1)
              (Fin.cons d coordinates) (sigmaFiber p) tail :=
        continuous_cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative_comp
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
                cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
                  (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
                  vertexBase vertexCoordinates W (n + 1)
                  (Fin.cons d coordinates) (sigmaFiber (x, t)) tail)
            (∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber (A, t)) tail)
            A := by
        apply
          hasFDerivAt_intervalIntegral_of_continuous_fieldDerivative_banach
            (F := fun p : PhysicalField M Q Nc × ℝ =>
              cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J p.1
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber p) tail)
            (F' := fun p : PhysicalField M Q Nc × ℝ =>
              cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J p.1
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates) (sigmaFiber p) tail)
            A hfirstPair.snd hsecond
        intro x t
        exact ih (A := x) (n := n + 1)
          (coordinates := Fin.cons d coordinates)
          (sigma := sigmaFiber (x, t))
          (hsigmaFiberRegion (x, t))
      have hfunEq :
          (fun x : PhysicalField M Q Nc =>
              ∫ t in (0 : ℝ)..1,
                cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
                  (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
                  vertexBase vertexCoordinates W (n + 1)
                  (Fin.cons d coordinates)
                  (Function.update sigma d t) tail) =
            (fun x : PhysicalField M Q Nc =>
              ∫ t in (0 : ℝ)..1,
                cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
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
            cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
              vertexBase vertexCoordinates W (n + 1)
              (Fin.cons d coordinates) u tail)
          heq.symm
      have hderivEq :
          (∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates)
                (Function.update sigma d t) tail) =
            ∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
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
            cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase vertexCoordinates W (n + 1)
              (Fin.cons d coordinates) u tail)
          heq.symm
      have hintegral :
          HasFDerivAt
            (fun x : PhysicalField M Q Nc =>
              ∫ t in (0 : ℝ)..1,
                cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
                  (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
                  vertexBase vertexCoordinates W (n + 1)
                  (Fin.cons d coordinates)
                  (Function.update sigma d t) tail)
            (∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates)
                (Function.update sigma d t) tail)
            A := by
        rw [hfunEq, hderivEq]
        exact hintegralClamped
      simpa [
        cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative,
        cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative] using
        hbase.add hintegral

set_option maxHeartbeats 128000000 in
/-- The literal connected equation-(80) activity is twice continuously
Fréchet differentiable in the physical field. -/
theorem contDiff_two_cmp102Eq80SourcePi4ConnectedDomainActivity
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
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ 2 fun A =>
      cmp102Eq80SourcePi4ConnectedDomainActivity
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates s L W := by
  let f :=
    fun A : PhysicalField M Q Nc =>
      cmp102Eq80SourcePi4ConnectedDomainActivity
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates s L W
  let f' :=
    fun A : PhysicalField M Q Nc =>
      cmp102Eq80SourcePi4ConnectedDomainFieldDerivative
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates s L W
  let f'' :=
    fun A : PhysicalField M Q Nc =>
      cmp102Eq80SourcePi4ConnectedDomainSecondFieldDerivative
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates s L W
  have hfirstAt (A : PhysicalField M Q Nc) :
      HasFDerivAt f (f' A) A := by
    simpa [f, f',
      cmp102Eq80SourcePi4ConnectedDomainActivity,
      cmp102Eq80SourcePi4ConnectedDomainFieldDerivative] using
      cmp102Eq80SourcePi4FTCConnectedDomainActivity_hasFDerivAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        hAhead hrho hrate Cert htri hrange hΔ hΔ1
        vertexBase vertexCoordinates W Fin.elim0 s L
        hRweak hs hsmall hD hD₃ hV₀
  have hsecondAt (A : PhysicalField M Q Nc) :
      HasFDerivAt f' (f'' A) A := by
    simpa [f', f'',
      cmp102Eq80SourcePi4ConnectedDomainFieldDerivative,
      cmp102Eq80SourcePi4ConnectedDomainSecondFieldDerivative] using
      cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative_hasFDerivAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        hAhead hrho hrate Cert htri hrange hΔ hΔ1
        vertexBase vertexCoordinates W Fin.elim0 s L
        hRweak hs hsmall hD hD₃ hV₀
  have hfirstPair :
      Continuous fun A : PhysicalField M Q Nc =>
        (f A, f' A) := by
    simpa [f, f',
      cmp102Eq80SourcePi4ConnectedDomainActivity,
      cmp102Eq80SourcePi4ConnectedDomainFieldDerivative] using
      continuous_cmp102Eq80SourcePi4FTCConnectedDomainActivity_and_fieldDerivative_comp
        anchor K hc hmass hK D D₃ V₀ Δπ J
        hAhead hrho hrate Cert htri hrange hΔ hΔ1
        (fun A : PhysicalField M Q Nc => A) continuous_id
        vertexBase vertexCoordinates W 0 Fin.elim0
        (fun _A => s) L
        (fun _d => continuous_const)
        hRweak (fun _A => hs) hsmall hD hD₃ hV₀
  have hsecondContinuous : Continuous f'' := by
    simpa [f'',
      cmp102Eq80SourcePi4ConnectedDomainSecondFieldDerivative] using
      continuous_cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative_comp
        anchor K hc hmass hK D D₃ V₀ Δπ J
        hAhead hrho hrate Cert htri hrange hΔ hΔ1
        (fun A : PhysicalField M Q Nc => A) continuous_id
        vertexBase vertexCoordinates W 0 Fin.elim0
        (fun _A => s) L
        (fun _d => continuous_const)
        hRweak (fun _A => hs) hsmall hD hD₃ hV₀
  have hfirstContDiff : ContDiff ℝ 1 f' :=
    contDiff_one_iff_hasFDerivAt.mpr
      ⟨f'', hsecondContinuous, hsecondAt⟩
  have hsecondContDiff : ContDiff ℝ (1 + 1) f :=
    contDiff_succ_iff_hasFDerivAt.mpr
      ⟨f', hfirstContDiff, hfirstAt⟩
  simpa [f] using hsecondContDiff

end

end YangMills.RG
