import YangMills.RG.BalabanCMP116CenteredConditionedEq80PartialPotential
import YangMills.RG.BalabanCMP116Eq226CenteredConditionedPhysicalTermSource

/-!
# Non-circular assembly of the centered conditioned term source

The generated structure constructor places equation `(1.36)` between the
quadratic-kernel fields and the scalar ledger.  For the physical constructor
we need the opposite dependency order: every independent field remains
visible, while `(1.36)` is produced last from the literal equation-(80)
residual and the named Lemma-1 certificate.

The private helper below merely reorders the generated constructor.  It is not
a source producer and is deliberately not exported.  The public constructor
in this module must supply its last argument internally; consequently there
is no public `eq136` premise or partially inhabited `TermSource`.
-/

namespace YangMills.RG

noncomputable section

private abbrev ConstructorBond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

private noncomputable def
    assembleCMP116Eq226CenteredConditionedPhysicalTermSource
    {nDelta nY M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (Y0 P : Finset (ConstructorBond M Q))
    (Z0 Z : Finset (FinBox 4 (2 * Q))) :=
  fun base
      anchor contourCarrier carrier_subset_sigmaZero carrier_subset_Z0
      Z0_subset_Z contourEquiv K root sourceRange sourceRange_bound
      finiteRange coercivityConstant mass coercivity_pos mass_pos K_coercive
      patchedDefect_small Ahead rho rate radius Ahead_nonneg rho_nonneg
      rate_pos shell_small patchCertificate distance_triangle Delta
      degree_bound one_le_Delta radius_nonneg radius_cap contour_series_small
      neumann_small neumann_transpose_small total residual smooth
      kernelSupport domainMetric domainCard domainSupport E0 epsilon1 C1
      alpha4 C3 C2 kappa1 delta kappa gk rowSum threshold alpha gamma q
      gapScale gapCard qBound qBound_nonneg qBound_lt_one rootBound
      volumeRate conditionedCovariance conditionedRoot
      conditionedCovariance_nondegenerate E0_pos epsilon1_pos C1_pos
      alpha4_pos C3_nonneg C3_le one_le_M eight_le_q one_lt_kappa1
      source_budget domainMetric_nonneg exponential_row_bound metric_budget
      hessian_zero_off_support eq143 interaction_budget deltaRadius_eq
      normalizedGap yRadius_eq gk_ne threshold_eq alpha_nonneg root_small
      gamma_nonneg threshold_nonneg outer_small domain_nonempty domain_subset
      rootBound_nonneg rooted_residual volume_budget eq136 =>
    ({
      base := base
      anchor := anchor
      contourCarrier := contourCarrier
      carrier_subset_sigmaZero := carrier_subset_sigmaZero
      carrier_subset_Z0 := carrier_subset_Z0
      Z0_subset_Z := Z0_subset_Z
      contourEquiv := contourEquiv
      K := K
      root := root
      sourceRange := sourceRange
      sourceRange_bound := sourceRange_bound
      finiteRange := finiteRange
      coercivityConstant := coercivityConstant
      mass := mass
      coercivity_pos := coercivity_pos
      mass_pos := mass_pos
      K_coercive := K_coercive
      patchedDefect_small := patchedDefect_small
      Ahead := Ahead
      rho := rho
      rate := rate
      radius := radius
      Ahead_nonneg := Ahead_nonneg
      rho_nonneg := rho_nonneg
      rate_pos := rate_pos
      shell_small := shell_small
      patchCertificate := patchCertificate
      distance_triangle := distance_triangle
      Delta := Delta
      degree_bound := degree_bound
      one_le_Delta := one_le_Delta
      radius_nonneg := radius_nonneg
      radius_cap := radius_cap
      contour_series_small := contour_series_small
      neumann_small := neumann_small
      neumann_transpose_small := neumann_transpose_small
      total := total
      residual := residual
      smooth := smooth
      kernelSupport := kernelSupport
      domainMetric := domainMetric
      domainCard := domainCard
      domainSupport := domainSupport
      E0 := E0
      epsilon1 := epsilon1
      C1 := C1
      alpha4 := alpha4
      C3 := C3
      C2 := C2
      kappa1 := kappa1
      delta := delta
      kappa := kappa
      gk := gk
      rowSum := rowSum
      threshold := threshold
      alpha := alpha
      gamma := gamma
      q := q
      gapScale := gapScale
      gapCard := gapCard
      qBound := qBound
      qBound_nonneg := qBound_nonneg
      qBound_lt_one := qBound_lt_one
      rootBound := rootBound
      volumeRate := volumeRate
      conditionedCovariance := conditionedCovariance
      conditionedRoot := conditionedRoot
      conditionedCovariance_nondegenerate :=
        conditionedCovariance_nondegenerate
      E0_pos := E0_pos
      epsilon1_pos := epsilon1_pos
      C1_pos := C1_pos
      alpha4_pos := alpha4_pos
      C3_nonneg := C3_nonneg
      C3_le := C3_le
      one_le_M := one_le_M
      eight_le_q := eight_le_q
      one_lt_kappa1 := one_lt_kappa1
      source_budget := source_budget
      domainMetric_nonneg := domainMetric_nonneg
      exponential_row_bound := exponential_row_bound
      metric_budget := metric_budget
      hessian_zero_off_support := hessian_zero_off_support
      eq143 := eq143
      eq136 := eq136
      interaction_budget := interaction_budget
      deltaRadius_eq := deltaRadius_eq
      normalizedGap := normalizedGap
      yRadius_eq := yRadius_eq
      gk_ne := gk_ne
      threshold_eq := threshold_eq
      alpha_nonneg := alpha_nonneg
      root_small := root_small
      gamma_nonneg := gamma_nonneg
      threshold_nonneg := threshold_nonneg
      outer_small := outer_small
      domain_nonempty := domain_nonempty
      domain_subset := domain_subset
      rootBound_nonneg := rootBound_nonneg
      rooted_residual := rooted_residual
      volume_budget := volume_budget
    } : CMP116Eq226CenteredConditionedPhysicalTermSource
      (nDelta := nDelta) (nY := nY) Dict Y0 P Z0 Z)

end

end YangMills.RG
