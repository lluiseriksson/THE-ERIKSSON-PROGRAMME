/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailSourceMetricDecay

/-!
# Entrywise source decay for the literal CMP102 equation-(80) coefficient

The matrix `L∞` norm is a maximum absolute row sum, so it controls every
entry of a rectangular matrix with constant one.  Applying this observation
to the complete fixed-domain coefficient preserves both source factors

`exp (-κcard * |Y|)` and `exp (-κmetric * d_k(Y))`

without reconstructing a finite-dimensional operator and therefore without
introducing an ambient-volume constant.

Honest scope: this is the kernel of the literal equation-(80) coefficient.
Identifying it with the radial Taylor operator of the specified source core
`V_k - V''_k` remains a separate dictionary theorem; this module does not
rename the coefficient as the full CMP116 `Q(Y,B)`.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator BigOperators

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- Every entry of a finite rectangular complex matrix is bounded by its
matrix `L∞` operator norm.  No cardinality factor is introduced. -/
theorem norm_rectangular_matrix_entry_le_linfty_opNorm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (i : ι) (j : κ) :
    ‖A i j‖ ≤ ‖A‖ := by
  calc
    ‖A i j‖ ≤ ∑ k : κ, ‖A i k‖ := by
      exact Finset.single_le_sum
        (fun k _ => norm_nonneg (A i k)) (Finset.mem_univ j)
    _ ≤ ‖A‖ := by
      rw [Matrix.linfty_opNorm_def]
      have hnn :
          (∑ k : κ, ‖A i k‖₊) ≤
            (Finset.univ : Finset ι).sup
              (fun r : ι => ∑ k : κ, ‖A r k‖₊) :=
        Finset.le_sup
          (s := (Finset.univ : Finset ι))
          (f := fun r : ι => ∑ k : κ, ‖A r k‖₊)
          (Finset.mem_univ i)
      have hreal :
          ((show NNReal from ∑ k : κ, ‖A i k‖₊) : ℝ) ≤
            ((show NNReal from
              (Finset.univ : Finset ι).sup
                (fun r : ι => ∑ k : κ, ‖A r k‖₊)) : ℝ) :=
        NNReal.coe_le_coe.mpr hnn
      simpa using hreal

/-- Entrywise source decay for the complete literal equation-(80) domain
coefficient.  The bound has exactly the same uniform prefactor as the
matrix row-norm theorem. -/
theorem
    norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient_entry_le_sourceMetricDecay
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (Y : CMP116LocalizationDomain M (2 * Q))
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 ≤ κcard)
    (hκmetric : 0 ≤ κmetric)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (i : FineCoord M Q Nc) (j : CoarseCoord Q Nc) :
    ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y.blocks i j‖ ≤
      cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
          (M := M) baseCoarseCovariance
          κcard κmetric summationRatio layerWord Y *
        (1 -
          ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio)⁻¹ := by
  exact
    (norm_rectangular_matrix_entry_le_linfty_opNorm
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y.blocks) i j).trans
      (norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient_le_sourceMetricDecay
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap layerWord choice Y
        hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
        hsplit hcardDecay hmetricDecay hsmall)

end

end YangMills.RG
