/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FaaDiBrunoPhysicalDomainContinuity

/-!
# Connected-domain localization of one literal FTC segment

The physical FTC tree varies one weakening coordinate over `[0,1]`.  The
uniform convergence proof for the completed random-walk coefficients is most
convenient on a globally bounded contour.  We therefore retract the real
line continuously onto `[0,1]`, prove that the resulting coordinate path
stays in the physical contour region globally, and then use equality on the
actual integration interval.

The terminal theorem localizes the literal, unclamped FTC segment.  The
clamping map is absent from its statement.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Continuous retraction of the real line onto the unit interval. -/
def cmp116ClampUnit (t : ℝ) : ℝ :=
  max 0 (min 1 t)

theorem continuous_cmp116ClampUnit :
    Continuous cmp116ClampUnit := by
  unfold cmp116ClampUnit
  fun_prop

theorem cmp116ClampUnit_nonneg (t : ℝ) :
    0 ≤ cmp116ClampUnit t := by
  exact le_max_left _ _

theorem cmp116ClampUnit_le_one (t : ℝ) :
    cmp116ClampUnit t ≤ 1 := by
  unfold cmp116ClampUnit
  exact max_le zero_le_one (min_le_left _ _)

@[simp] theorem cmp116ClampUnit_eq_self {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cmp116ClampUnit t = t := by
  rcases ht with ⟨ht0, ht1⟩
  simp [cmp116ClampUnit, min_eq_right ht1, max_eq_right ht0]

/-- Globally bounded version of the literal one-coordinate FTC path. -/
def cmp116ClampedRealWeakeningCoordinatePath
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (d : D) (t : ℝ) : D → ℝ :=
  Function.update s d (cmp116ClampUnit t)

theorem continuous_cmp116ClampedRealWeakeningCoordinatePath_apply
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (d x : D) :
    Continuous fun t =>
      cmp116ClampedRealWeakeningCoordinatePath s d t x := by
  by_cases hxd : x = d
  · subst x
    simpa [cmp116ClampedRealWeakeningCoordinatePath] using
      continuous_cmp116ClampUnit
  · have hdx : d ≠ x := Ne.symm hxd
    simpa [cmp116ClampedRealWeakeningCoordinatePath,
      Function.update, hxd, hdx] using
      (continuous_const : Continuous (fun _ : ℝ => s x))

/-- The clamped coordinate path stays in the physical real contour region
for all real parameters. -/
theorem cmp116ClampedRealWeakeningCoordinatePath_mem_contourRegion
    {D : Type*} [DecidableEq D]
    (Rweak : ℝ) (hRweak : 1 ≤ Rweak)
    (s : D → ℝ) (hs : CMP116RealPhysicalContourRegion Rweak s)
    (d : D) (t : ℝ) :
    CMP116RealPhysicalContourRegion Rweak
      (cmp116ClampedRealWeakeningCoordinatePath s d t) := by
  constructor
  · intro x
    by_cases hxd : x = d
    · subst x
      simp only [cmp116ClampedRealWeakeningCoordinatePath,
        Function.update_self]
      have habs : |cmp116ClampUnit t - 1| ≤ 1 := by
        rw [abs_of_nonpos]
        · linarith [cmp116ClampUnit_nonneg t]
        · linarith [cmp116ClampUnit_le_one t]
      have heq :
          (cmp116ClampUnit t : ℂ) - 1 =
            ((cmp116ClampUnit t - 1 : ℝ) : ℂ) := by
        norm_num
      rw [heq, Complex.norm_real]
      exact habs
    · have hdx : d ≠ x := Ne.symm hxd
      simpa [cmp116ClampedRealWeakeningCoordinatePath,
        Function.update, hxd, hdx] using hs.1 x
  · intro x
    by_cases hxd : x = d
    · subst x
      simp only [cmp116ClampedRealWeakeningCoordinatePath,
        Function.update_self]
      have habs : |cmp116ClampUnit t| ≤ Rweak := by
        rw [abs_of_nonneg (cmp116ClampUnit_nonneg t)]
        exact (cmp116ClampUnit_le_one t).trans hRweak
      simpa [Complex.norm_real] using habs
    · have hdx : d ≠ x := Ne.symm hxd
      simpa [cmp116ClampedRealWeakeningCoordinatePath,
        Function.update, hxd, hdx] using hs.2 x

@[simp] theorem cmp116ClampedRealWeakeningCoordinatePath_eq_update
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (d : D) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cmp116ClampedRealWeakeningCoordinatePath s d t =
      Function.update s d t := by
  simp [cmp116ClampedRealWeakeningCoordinatePath,
    cmp116ClampUnit_eq_self ht]

set_option maxHeartbeats 20000000 in
/-- One literal coordinate segment of the physical FTC expansion is exactly
the sum of the integrated connected-domain coefficients. -/
theorem
    integral_coordinateSegment_iteratedFDeriv_cmp102Eq80SourcePi4RealPotentialVertexPolynomial_eq_sum_integral_connectedPhysicalDomains
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
    (vertexBase endpointS : FinBox 4 (2 * Q) → ℝ)
    (d : FinBox 4 (2 * Q))
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hcover : ∀ x : FinBox 4 (2 * Q), x ∈ L)
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (hinjective : Function.Injective coordinates)
    (hRweak : 1 ≤ Rweak)
    (hvertexBase : CMP116RealPhysicalContourRegion Rweak vertexBase)
    (hendpointS : CMP116RealPhysicalContourRegion Rweak endpointS)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ n V₀) :
    (∫ t in (0 : ℝ)..1,
      iteratedFDeriv ℝ n
        (fun tau =>
          cmp102Eq80SourcePi4RealPotentialVertexPolynomial
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            vertexBase L tau A)
        (Function.update endpointS d t)
        (fun i => Pi.single (coordinates i) 1)) =
      ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
        ∫ t in (0 : ℝ)..1,
          cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase (Function.update endpointS d t)
            L coordinates W := by
  classical
  let sigma : ℝ → FinBox 4 (2 * Q) → ℝ :=
    cmp116ClampedRealWeakeningCoordinatePath endpointS d
  have hsigma (x : FinBox 4 (2 * Q)) :
      Continuous fun t => sigma t x :=
    continuous_cmp116ClampedRealWeakeningCoordinatePath_apply
      endpointS d x
  have hsigmaRegion (t : ℝ) :
      CMP116RealPhysicalContourRegion Rweak (sigma t) :=
    cmp116ClampedRealWeakeningCoordinatePath_mem_contourRegion
      Rweak hRweak endpointS hendpointS d t
  have hclamped :=
    integral_iteratedFDeriv_cmp102Eq80SourcePi4RealPotentialVertexPolynomial_eq_sum_integral_connectedPhysicalDomains
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      vertexBase sigma hsigma L hL hcover coordinates hinjective
      hRweak hvertexBase hsigmaRegion hsmall hV₀ 0 1
  calc
    _ = ∫ t in (0 : ℝ)..1,
        iteratedFDeriv ℝ n
          (fun tau =>
            cmp102Eq80SourcePi4RealPotentialVertexPolynomial
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
              vertexBase L tau A)
          (sigma t) (fun i => Pi.single (coordinates i) 1) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le zero_le_one] using ht
      have heq : sigma t = Function.update endpointS d t :=
        cmp116ClampedRealWeakeningCoordinatePath_eq_update
          endpointS d ht'
      change
        iteratedFDeriv ℝ n
            (fun tau =>
              cmp102Eq80SourcePi4RealPotentialVertexPolynomial
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
                vertexBase L tau A)
            (Function.update endpointS d t)
            (fun i => Pi.single (coordinates i) 1) =
          iteratedFDeriv ℝ n
            (fun tau =>
              cmp102Eq80SourcePi4RealPotentialVertexPolynomial
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
                vertexBase L tau A)
            (sigma t) (fun i => Pi.single (coordinates i) 1)
      rw [heq]
    _ = ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
          ∫ t in (0 : ℝ)..1,
            cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase (sigma t) L coordinates W := hclamped
    _ = _ := by
      apply Finset.sum_congr rfl
      intro W _hW
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le zero_le_one] using ht
      have heq : sigma t = Function.update endpointS d t :=
        cmp116ClampedRealWeakeningCoordinatePath_eq_update
          endpointS d ht'
      change
        cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase (sigma t) L coordinates W =
          cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase (Function.update endpointS d t)
            L coordinates W
      rw [heq]

end

end YangMills.RG
