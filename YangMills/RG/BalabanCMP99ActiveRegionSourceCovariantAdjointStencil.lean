import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport
import YangMills.RG.BalabanCMP99Eq342SourceLocalizedGreenCertificate
import YangMills.RG.BalabanCMP99Eq389BlockShiftGeometry
import YangMills.RG.FinitePiLpBlockLocalizedSupAlgebra

/-!
# Regional covariant-adjoint stencil and owner support

The literal regional derivative adjoint is identified with the restricted
backward divergence.  Its finite-supremum budget and radius-one owner support
are then derived from that stencil.  No Green symmetry or coordinate-probe
expansion is used.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Draft C6c.4d7a.  The counting-Hilbert adjoint of the literal regional
scaled derivative is the restricted backward divergence.  No symmetry of a
Green kernel is used here. -/
theorem cmp99ActiveRegionSourceCovariantD0CLM_adjoint_apply
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ)
    (f : PhysicalGaugeOneCochain d N Nc)
    (x : ActiveGaugeRegion.Site Omega) :
    (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).adjoint f x =
      spacing⁻¹ •
        ∑ i : Fin d,
          (f (x.1, i) -
            rho.adCLM
              (U (positiveEdgeOfPhysicalBond
                ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
              (f (x.1.shiftBack i, i))) := by
  let E : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      PhysicalGaugeZeroCochain d N Nc := extendZeroZeroCLM Omega
  let R : PhysicalGaugeZeroCochain d N Nc →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) := restrictZeroCLM Omega
  have hR : R = E.adjoint :=
    cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint Omega
  change ((spacing⁻¹ • (covariantD0CLM rho U).comp E).adjoint f) x = _
  simp only [map_smul, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [← hR]
  change spacing⁻¹ • gaugeConstraintQCLM rho U f x = _
  rw [gaugeConstraintQCLM_apply_background]

/-- The regional adjoint divergence is bounded in finite supremum norm by
the literal `2d/spacing` stencil budget. -/
theorem finitePiLpSupNorm_cmp99ActiveRegionSourceCovariantD0CLM_adjoint_le
    (Omega : ActiveGaugeRegion d N) [Nonempty (ActiveGaugeRegion.Site Omega)]
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (f : PhysicalGaugeOneCochain d N Nc) :
    finitePiLpSupNorm
        ((cmp99ActiveRegionSourceCovariantD0CLM
          Omega rho U spacing).adjoint f) ≤
      (2 * d / spacing) * finitePiLpSupNorm f := by
  apply finitePiLpSupNorm_le_of_norm_apply_le
  intro x
  rw [cmp99ActiveRegionSourceCovariantD0CLM_adjoint_apply,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspacing)]
  calc
    spacing⁻¹ *
        ‖∑ i : Fin d,
          (f (x.1, i) -
            rho.adCLM
              (U (positiveEdgeOfPhysicalBond
                ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
              (f (x.1.shiftBack i, i)))‖ ≤
      spacing⁻¹ * ∑ i : Fin d,
        (‖f (x.1, i)‖ + ‖f (x.1.shiftBack i, i)‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hspacing.le)
      calc
        ‖∑ i : Fin d, _‖ ≤ ∑ i : Fin d, ‖_‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin d,
            (‖f (x.1, i)‖ + ‖f (x.1.shiftBack i, i)‖) := by
          gcongr with i
          calc
            ‖f (x.1, i) -
                rho.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
                  (f (x.1.shiftBack i, i))‖ ≤
              ‖f (x.1, i)‖ +
                ‖rho.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
                  (f (x.1.shiftBack i, i))‖ := norm_sub_le _ _
            _ = ‖f (x.1, i)‖ + ‖f (x.1.shiftBack i, i)‖ := by
              rw [rho.norm_ad]
    _ ≤ spacing⁻¹ * ∑ _i : Fin d,
        (finitePiLpSupNorm f + finitePiLpSupNorm f) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hspacing.le)
      exact Finset.sum_le_sum fun i _ =>
        add_le_add
          (norm_apply_le_finitePiLpSupNorm f (x.1, i))
          (norm_apply_le_finitePiLpSupNorm f (x.1.shiftBack i, i))
    _ = (2 * d / spacing) * finitePiLpSupNorm f := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      (field_simp [ne_of_gt hspacing]; ring)

private theorem finBoxEquivCast_shiftBack_draft
    {d N M : ℕ} [NeZero N] [NeZero M]
    (h : N = M) (x : FinBox d N) (i : Fin d) :
    Equiv.cast (congrArg (FinBox d) h) (x.shiftBack i) =
      (Equiv.cast (congrArg (FinBox d) h) x).shiftBack i := by
  subst M
  rfl

variable {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]

/-- A nonzero coordinate of the regional adjoint divergence lies in an
owner at source-localization distance at most one from the owner supporting
the input bond field. -/
theorem cmp99ActiveRegionSourceCovariantD0CLM_adjoint_apply_eq_zero_of_owner_far
    (depth : ℕ)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (spacing : ℝ)
    (owner : FinBox 4 (2 * (K * Q)))
    (f : PhysicalGaugeOneCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (hf : FinitePiLpSupportedInOwner
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth) owner f)
    (x : ActiveGaugeRegion.Site Omega)
    (hfar : ¬ finBoxDist
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth x) owner ≤ 1) :
    (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).adjoint f x = 0 := by
  rw [cmp99ActiveRegionSourceCovariantD0CLM_adjoint_apply]
  apply smul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i _hi
  have hforwardOwner :
      cmp99Eq342SourceLocalizedBondOwner L K Q depth (x.1, i) =
        cmp99Eq342SourceLocalizedActiveOwner L K Q depth x := rfl
  have hforwardNe :
      cmp99Eq342SourceLocalizedBondOwner L K Q depth (x.1, i) ≠ owner := by
    intro h
    apply hfar
    have hactive :
        cmp99Eq342SourceLocalizedActiveOwner L K Q depth x = owner :=
      hforwardOwner.symm.trans h
    rw [hactive, finBoxDist_self]
    omega
  have hbackNe :
      cmp99Eq342SourceLocalizedBondOwner L K Q depth
          (x.1.shiftBack i, i) ≠ owner := by
    intro h
    apply hfar
    have hcastShiftBack :
        cmp99Eq389SourceLocalizationSiteEquiv L K Q depth
            (x.1.shiftBack i) =
          (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth x.1).shiftBack i := by
      exact finBoxEquivCast_shiftBack_draft
        (cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier
          L K Q depth) x.1 i
    have hstep := finBoxDist_blockSite_shiftBack_le_one
      (m := L ^ (depth + 1)) (n := 2 * (K * Q))
      (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth x.1) i
    have hstep' :
        finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth x.1)
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (x.1.shiftBack i)) ≤ 1 := by
      simpa [cmp99Eq389SourceLocalizationOwner, hcastShiftBack] using hstep
    have hbackOwner :
        cmp99Eq389SourceLocalizationOwner L K Q depth (x.1.shiftBack i) =
          owner := by
      simpa [cmp99Eq342SourceLocalizedBondOwner] using h
    simpa [cmp99Eq342SourceLocalizedActiveOwner, hbackOwner] using hstep'
  rw [hf (x.1, i) hforwardNe, hf (x.1.shiftBack i, i) hbackNe]
  simp

end

end YangMills.RG
