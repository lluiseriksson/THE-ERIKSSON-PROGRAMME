/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4RealMixedWeakenedCovariance

/-!
# Source-produced derivative certificate for the real mixed covariance

The complete complex contour theorem first produces all scalar coordinate
derivatives.  A finite matrix-unit reconstruction then transports those
derivatives to the real physical endomorphism space.  Bundling the scalar
family keeps the elaborator from repeatedly normalizing the full physical
contour data; it does not add an analytic hypothesis.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The complete complex mixed covariance matrix when one real weakening
coordinate varies. -/
noncomputable def cmp116SourcePi4ComplexMixedCovarianceMatrixCurve
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q))
    (u : ℝ) :=
  cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
    (R := R) anchor K hc hmass hK
    (Function.update (fun x => (s x : ℂ)) d (u : ℂ)) S

/-- The next complete complex mixed covariance matrix. -/
noncomputable def cmp116SourcePi4ComplexMixedCovarianceMatrixDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) :=
  cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
    (R := R) anchor K hc hmass hK (fun x => (s x : ℂ)) (insert d S)

/-- The real mixed covariance curve obtained by varying one weakening
coordinate. -/
noncomputable def cmp116SourcePi4RealMixedCovarianceOperatorCurve
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q))
    (u : ℝ) : PhysicalEndomorphism M Q Nc :=
  cmp116PhysicalEndomorphismOfComplexMatrixCLM
    (cmp116SourcePi4ComplexMixedCovarianceMatrixCurve
      (R := R) anchor K hc hmass hK s S d u)

/-- The next real mixed covariance in the derivative recurrence. -/
noncomputable def cmp116SourcePi4RealMixedCovarianceOperatorDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) : PhysicalEndomorphism M Q Nc :=
  cmp116PhysicalEndomorphismOfComplexMatrixCLM
    (cmp116SourcePi4ComplexMixedCovarianceMatrixDerivative
      (R := R) anchor K hc hmass hK s S d)

/-- The named operator curve is literally the previously constructed real
mixed covariance with the selected weakening coordinate updated. -/
theorem cmp116SourcePi4RealMixedCovarianceOperatorCurve_eq
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q))
    (u : ℝ) :
    cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK s S d u =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK (Function.update s d u) S := by
  have hupdate :
      (fun x => ((Function.update s d u) x : ℂ)) =
        Function.update (fun x => (s x : ℂ)) d (u : ℂ) := by
    funext x
    by_cases hx : x = d
    · subst x
      simp
    · simp [Function.update_of_ne hx]
  unfold cmp116SourcePi4RealMixedCovarianceOperatorCurve
    cmp116SourcePi4ComplexMixedCovarianceMatrixCurve
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
  rw [hupdate]

/-- The named operator derivative is the next real mixed covariance. -/
theorem cmp116SourcePi4RealMixedCovarianceOperatorDerivative_eq
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) :
    cmp116SourcePi4RealMixedCovarianceOperatorDerivative
        (R := R) anchor K hc hmass hK s S d =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK s (insert d S) := by
  rfl

/-- The operator-valued derivative recurrence, kept behind a named
proposition so elaboration does not repeatedly normalize the full physical
endomorphism type. -/
def CMP116SourcePi4RealMixedOperatorDerivativeStatement
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q))
    (t : ℝ) : Prop :=
  HasDerivAt
    (cmp116SourcePi4RealMixedCovarianceOperatorCurve
      (R := R) anchor K hc hmass hK s S d)
    (cmp116SourcePi4RealMixedCovarianceOperatorDerivative
      (R := R) anchor K hc hmass hK s S d)
    t

/-- Finite coordinate derivative data for one source weakening coordinate. -/
structure CMP116SourcePi4RealMixedDerivativeCertificate
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q))
    (t : ℝ) : Prop where
  entryDerivative : ∀ row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc,
    HasDerivAt
      (cmp116SourcePi4RealMixedCovarianceEntryCurve
        (R := R) anchor K hc hmass hK s S d row col)
      (cmp116SourcePi4RealMixedCovarianceEntryDerivative
        (R := R) anchor K hc hmass hK s S d row col) t

set_option maxHeartbeats 1500000 in
/-- The complete physical contour theorem produces the entrywise certificate;
the caller supplies no derivative estimate. -/
theorem CMP116SourcePi4RealMixedDerivativeCertificate.ofPhysicalContour
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
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
    (t : ℝ) :
    CMP116SourcePi4RealMixedDerivativeCertificate
      (R := R) anchor K hc hmass hK s S d t := by
  constructor
  intro row col
  exact
    hasDerivAt_re_cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative_update
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 s S d hdS hRweak hs hcap hsmall row col t

set_option maxHeartbeats 1500000 in
/-- A source-produced coordinate certificate reconstructs to the derivative
of the real physical mixed covariance. -/
theorem CMP116SourcePi4RealMixedDerivativeCertificate.hasDerivAt_operator
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
    (Cert : CMP116SourcePi4RealMixedDerivativeCertificate
      (R := R) anchor K hc hmass hK s S d t) :
    CMP116SourcePi4RealMixedOperatorDerivativeStatement
      (R := R) anchor K hc hmass hK s S d t := by
  unfold CMP116SourcePi4RealMixedOperatorDerivativeStatement
  unfold cmp116SourcePi4RealMixedCovarianceOperatorCurve
    cmp116SourcePi4RealMixedCovarianceOperatorDerivative
  apply
    hasDerivAt_cmp116PhysicalEndomorphismOfComplexMatrixCLM_of_entrywise
  intro row col
  simpa [cmp116SourcePi4ComplexMixedCovarianceMatrixCurve,
    cmp116SourcePi4ComplexMixedCovarianceMatrixDerivative,
    cmp116SourcePi4RealMixedCovarianceEntryCurve,
    cmp116SourcePi4RealMixedCovarianceEntryDerivative] using
      Cert.entryDerivative row col

end

end YangMills.RG
