/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.SmoothSeries
import YangMills.RG.BalabanCMP116SourcePi4FullComplexContourDefect
import YangMills.RG.BalabanCMP116SourcePi4FullComplexWeakenedCovarianceDerivative

/-!
# Coordinate derivatives of the complete physical weakened covariance

The previous module differentiated every finite walk-length layer.  Here the
physical contour majorants are used to prove a summable bound for those
derivatives.  Only then is `hasDerivAt_tsum` applied to the length-ordered
series.

The derivative bound is not postulated.  The erased-coordinate derivative of
each layer is its exact unit finite difference, and the two endpoints are
controlled by the already-proved source `Pi^4` contour estimate.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Length-ordered derivative matrix of the complete weakened covariance. -/
noncomputable def
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q)) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  fun row col =>
    ∑' n : ℕ,
      cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative
        (R := R) anchor K hc hmass hK sigma d n row col

/-- A unit shifted-polydisc parameter stays admissible after setting one
coordinate equal to zero. -/
private theorem update_zero_unitShifted
    {Δ : Type*} [DecidableEq Δ]
    (sigma : Δ → ℂ) (d : Δ)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖Function.update sigma d 0 x - 1‖ ≤ (1 : ℝ) := by
  intro x
  by_cases hx : x = d
  · subst x
    simp
  · rw [Function.update_of_ne hx]
    exact hsigma x

/-- A unit shifted-polydisc parameter stays admissible after setting one
coordinate equal to one. -/
private theorem update_one_unitShifted
    {Δ : Type*} [DecidableEq Δ]
    (sigma : Δ → ℂ) (d : Δ)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖Function.update sigma d 1 x - 1‖ ≤ (1 : ℝ) := by
  intro x
  by_cases hx : x = d
  · subst x
    simp
  · rw [Function.update_of_ne hx]
    exact hsigma x

/-- The radial cap is preserved when one coordinate is set to zero. -/
private theorem update_zero_cap
    {Δ : Type*} [DecidableEq Δ]
    (sigma : Δ → ℂ) (d : Δ) (Rweak : ℝ)
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak) :
    ∀ x, ‖Function.update sigma d 0 x‖ ≤ Rweak := by
  intro x
  by_cases hx : x = d
  · subst x
    simpa using (norm_nonneg (sigma d)).trans (hcap d)
  · rw [Function.update_of_ne hx]
    exact hcap x

/-- The radial cap is preserved when one coordinate is set to one. -/
private theorem update_one_cap
    {Δ : Type*} [DecidableEq Δ]
    (sigma : Δ → ℂ) (d : Δ) (Rweak : ℝ)
    (hRweak : 1 ≤ Rweak) (hcap : ∀ x, ‖sigma x‖ ≤ Rweak) :
    ∀ x, ‖Function.update sigma d 1 x‖ ≤ Rweak := by
  intro x
  by_cases hx : x = d
  · subst x
    simpa using hRweak
  · rw [Function.update_of_ne hx]
    exact hcap x

/-- The physical contour estimate gives a summable bound for each scalar
coordinate derivative layer. -/
theorem
    norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative_apply_le
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
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
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (n : ℕ)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    ‖cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative
        (R := R) anchor K hc hmass hK sigma d n row col‖ ≤
      2 * (cmp116SourcePi4ComplexDefectLayerAmplitude
          Δ Ahead rho 1 Rweak n *
        Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ)))) := by
  let oneLayer :=
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK (fun _ => 1) n
  let atOne :=
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK
      (Function.update sigma d 1) n
  let atZero :=
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK
      (Function.update sigma d 0) n
  have hOne :=
    norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_apply_le'
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      (Function.update sigma d 1) (by positivity) hRweak
      (update_one_unitShifted sigma d hsigma)
      (update_one_cap sigma d Rweak hRweak hcap) n row col
  have hZero :=
    norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_apply_le'
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      (Function.update sigma d 0) (by positivity) hRweak
      (update_zero_unitShifted sigma d hsigma)
      (update_zero_cap sigma d Rweak hcap) n row col
  calc
    ‖cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative
        (R := R) anchor K hc hmass hK sigma d n row col‖ =
        ‖(atOne row col - oneLayer row col) -
          (atZero row col - oneLayer row col)‖ := by
      rw [
        cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative_eq_sub]
      simp only [Matrix.sub_apply]
      congr 1
      ring
    _ ≤ ‖atOne row col - oneLayer row col‖ +
        ‖atZero row col - oneLayer row col‖ := norm_sub_le _ _
    _ ≤ cmp116SourcePi4ComplexDefectLayerAmplitude
          Δ Ahead rho 1 Rweak n *
          Real.exp (-(rate *
            (physicalBondDist row.1 col.1 : ℝ))) +
        cmp116SourcePi4ComplexDefectLayerAmplitude
          Δ Ahead rho 1 Rweak n *
          Real.exp (-(rate *
            (physicalBondDist row.1 col.1 : ℝ))) :=
      add_le_add hOne hZero
    _ = 2 * (cmp116SourcePi4ComplexDefectLayerAmplitude
          Δ Ahead rho 1 Rweak n *
        Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ)))) := by ring

/-- The complete physical length-ordered covariance is differentiable in
each weakening coordinate.  The theorem invokes `hasDerivAt_tsum` only after
constructing the explicit summable derivative majorant. -/
theorem
    hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_update
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
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
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (t : ℂ) :
    HasDerivAt
      (fun z =>
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK
          (Function.update sigma d z) row col)
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixDerivative
        (R := R) anchor K hc hmass hK sigma d row col)
      t := by
  let decay : ℝ :=
    Real.exp (-(rate *
      (physicalBondDist row.1 col.1 : ℝ)))
  let u : ℕ → ℝ := fun n =>
    2 * (cmp116SourcePi4ComplexDefectLayerAmplitude
      Δ Ahead rho 1 Rweak n * decay)
  have hu : Summable u := by
    have hamp :=
      (hasSum_cmp116SourcePi4ComplexDefectLayerAmplitude
        Δ Ahead rho 1 Rweak hsmall).summable
    exact ((hamp.mul_right decay).mul_left 2)
  have hbaseMatrix :
      Summable fun n : ℕ =>
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK
          (Function.update sigma d 1) n := by
    let diffLayer := fun n : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK
          (Function.update sigma d 1) n -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) n
    let oneLayer := fun n : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) n
    have hdiff : Summable diffLayer :=
      summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 (Function.update sigma d 1) (by positivity) hRweak
        (update_one_unitShifted sigma d hsigma)
        (update_one_cap sigma d Rweak hRweak hcap) hsmall
    have hone : Summable oneLayer :=
      summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 hRweak hsmall
    exact (hdiff.add hone).congr fun n => by
      dsimp [diffLayer, oneLayer]
      exact sub_add_cancel _ _
  have hbase : Summable fun n : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK
        (Function.update sigma d 1) n row col :=
    Pi.summable.mp (Pi.summable.mp hbaseMatrix row) col
  have hseries := hasDerivAt_tsum
    (g := fun n z =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK
        (Function.update sigma d z) n row col)
    (g' := fun n _ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative
        (R := R) anchor K hc hmass hK sigma d n row col)
    (u := u) (y₀ := (1 : ℂ))
    hu
    (fun n z =>
      hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_update
        anchor K hc hmass hK sigma d n row col z)
    (fun n _ =>
      norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative_apply_le
        anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
        sigma d hRweak hsigma hcap n row col)
    hbase t
  simpa [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix,
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixDerivative, decay, u]
    using hseries

end

end YangMills.RG
