/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116PhysicalEndomorphismMatrixReconstruction
import YangMills.RG.BalabanCMP116SourcePi4MixedWeakenedCovarianceDerivativeSeries

/-!
# Real operator reconstruction of the mixed source covariance

The convergent complex covariance matrix is reconstructed as a real physical
endomorphism by taking its real coordinate matrix.  At full coupling this is
proved equal to the exact physical covariance.  Entrywise mixed derivative
theorems are transported through the finite matrix-unit reconstruction, so
the resulting derivative lives in the physical operator space consumed by
the CMP102 potential.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

local instance : ContinuousSMul ℝ ℂ := {
  continuous_smul := by
    simpa [Complex.real_smul] using
      (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
}

/-- Reconstructed real physical operator associated with a complete complex
mixed covariance at real weakening parameters. -/
noncomputable def
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q))) :
    PhysicalEndomorphism M Q Nc :=
  cmp116PhysicalEndomorphismOfComplexMatrixCLM
    (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
      (R := R) anchor K hc hmass hK (fun x => (s x : ℂ)) S)

/-- One real coordinate curve of a mixed covariance when a fresh weakening
coordinate varies. -/
noncomputable def cmp116SourcePi4RealMixedCovarianceEntryCurve
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (u : ℝ) : ℝ :=
  (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
    (R := R) anchor K hc hmass hK
    (Function.update (fun x => (s x : ℂ)) d (u : ℂ))
    S row col).re

/-- The next mixed covariance entry, reconstructed over the real field. -/
noncomputable def cmp116SourcePi4RealMixedCovarianceEntryDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) : ℝ :=
  (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
    (R := R) anchor K hc hmass hK (fun x => (s x : ℂ))
    (insert d S) row col).re

/-- At full coupling, the reconstructed empty mixed derivative is the exact
physical covariance. -/
theorem
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_empty_one_eq_exact
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK (fun _ => 1) ∅ =
      cmp116SourcePi4QuotientExactPatchedCovariance
        K hc hmass hK := by
  have hempty :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
          (R := R) anchor K hc hmass hK (fun _ => (1 : ℂ)) ∅ =
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) := by
    funext row col
    apply tsum_congr
    intro n
    exact congrFun (congrFun
      (cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_empty
        anchor K hc hmass hK (fun _ => (1 : ℂ)) n) row) col
  unfold cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
  change
    cmp116PhysicalEndomorphismOfComplexMatrixCLM
        (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
          (R := R) anchor K hc hmass hK (fun _ => (1 : ℂ)) ∅) =
      cmp116SourcePi4QuotientExactPatchedCovariance K hc hmass hK
  rw [hempty,
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD,
    cmp116PhysicalEndomorphismOfComplexMatrixCLM_canonical]

set_option maxHeartbeats 1200000 in
/-- Entrywise real-part derivative inherited from the complete complex mixed
covariance. -/
theorem
    hasDerivAt_re_cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative_update
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
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) (hdS : d ∉ S)
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (t : ℝ) :
    HasDerivAt
      (cmp116SourcePi4RealMixedCovarianceEntryCurve
        (R := R) anchor K hc hmass hK s S d row col)
      (cmp116SourcePi4RealMixedCovarianceEntryDerivative
        (R := R) anchor K hc hmass hK s S d row col) t := by
  have hcomplex :=
    (hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative_update
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 (fun x => (s x : ℂ)) S d hdS hRweak hs hcap hsmall row col
      (t : ℂ)).comp_ofReal
  have hre : HasDerivAt
      (fun u : ℝ =>
        (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
          (R := R) anchor K hc hmass hK
          (Function.update (fun x => (s x : ℂ)) d (u : ℂ))
          S row col).re)
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
        (R := R) anchor K hc hmass hK (fun x => (s x : ℂ))
        (insert d S) row col).re t := by
    simpa [Function.comp_def, Complex.reCLM_apply] using
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hcomplex)
  simpa [cmp116SourcePi4RealMixedCovarianceEntryCurve,
    cmp116SourcePi4RealMixedCovarianceEntryDerivative] using hre

/-
The direct monolithic corollary is intentionally deferred to a small
certificate module: elaborating all physical contour data and the
operator-valued derivative in one declaration exceeds the normalizer budget.
The two compiled producers above compose through
`hasDerivAt_cmp116PhysicalEndomorphismOfComplexMatrixCLM_of_entrywise`.

set_option maxHeartbeats 3000000 in
/-- Entrywise source derivatives reconstruct to the derivative of the real
physical operator.  The preceding theorem is the source-specific producer
of `hentry`; this theorem contains no analytic estimate of its own. -/
theorem
    hasDerivAt_cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_update_of_entrywise
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q))
    (t : ℝ)
    (hentry : ∀ row col : CMP116PhysicalWalkCoordinate
        4 (M * (2 * Q)) Nc,
      HasDerivAt
        (cmp116SourcePi4RealMixedCovarianceEntryCurve
          (R := R) anchor K hc hmass hK s S d row col)
        (cmp116SourcePi4RealMixedCovarianceEntryDerivative
          (R := R) anchor K hc hmass hK s S d row col) t) :
    HasDerivAt
      (fun u =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK
          (Function.update s d u) S)
      (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK s (insert d S))
      t := by
  let sigma : FinBox 4 (2 * Q) → ℂ := fun x => (s x : ℂ)
  let A := fun u : ℝ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
      (R := R) anchor K hc hmass hK
      (Function.update sigma d (u : ℂ)) S
  let A' :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
      (R := R) anchor K hc hmass hK sigma (insert d S)
  have hentry' : ∀ row col,
      HasDerivAt (fun u => (A u row col).re) (A' row col).re t := by
    intro row col
    simpa [A, A', sigma, cmp116SourcePi4RealMixedCovarianceEntryCurve,
      cmp116SourcePi4RealMixedCovarianceEntryDerivative] using hentry row col
  have hreconstructed :=
    hasDerivAt_cmp116PhysicalEndomorphismOfComplexMatrixCLM_of_entrywise
      A A' t hentry'
  have hupdate : ∀ u : ℝ,
      (fun x => ((Function.update s d u) x : ℂ)) =
        Function.update sigma d (u : ℂ) := by
    intro u
    funext x
    by_cases hx : x = d
    · subst x
      simp
    · simp [Function.update_of_ne hx, sigma]
  convert hreconstructed using 1
  · funext u
    unfold cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
    rw [hupdate u]
    rfl
  · unfold cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
    rfl
-/

end

end YangMills.RG
