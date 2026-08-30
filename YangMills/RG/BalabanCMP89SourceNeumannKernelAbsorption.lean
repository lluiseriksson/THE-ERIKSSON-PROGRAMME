import YangMills.RG.BalabanCMP89SourceNeumannRegionalGaugePrecision

/-!
# Quantitative absorption of the CMP89 Neumann joint kernel

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

This leaf isolates the exact scalar endpoint of the recursive Neumann
argument.  A regional Poincare estimate absorbs an approximate derivative
kernel whenever the averaging component vanishes and the visible product
`CP * kappa` is strictly below one.

No recursive dictionary is asserted here.  In particular, the theorem does
not identify the coarse field, its background, or its averaging operator;
those remain the source-specific inputs needed to consume the quantitative
defect estimate.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- A Neumann Poincare estimate absorbs a derivative defect below its
explicit scalar threshold.  The conclusion is exact; the strict window
`CP * kappa < 1` is not weakened or hidden in a renamed constant. -/
theorem eq_zero_of_cmp89SourceNeumannRegionalPoincare_of_derivative_sq_le
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing CP kappa : ℝ)
    (hCP : 0 < CP)
    (hP : CMP89SourceNeumannRegionalPoincare
      Omega rho U Qprime spacing CP)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hQ : Qprime phi = 0)
    (hD : ‖cmp89SourceNeumannRegionalCovariantD0CLM
      Omega rho U spacing phi‖ ^ 2 ≤ kappa * ‖phi‖ ^ 2)
    (hsmall : CP * kappa < 1) :
    phi = 0 := by
  have hPphi : ‖phi‖ ^ 2 ≤ CP *
      ‖cmp89SourceNeumannRegionalCovariantD0CLM
        Omega rho U spacing phi‖ ^ 2 := by
    simpa [hQ] using hP phi
  have habsorb : ‖phi‖ ^ 2 ≤ (CP * kappa) * ‖phi‖ ^ 2 := by
    calc
      ‖phi‖ ^ 2 ≤ CP *
          ‖cmp89SourceNeumannRegionalCovariantD0CLM
            Omega rho U spacing phi‖ ^ 2 := hPphi
      _ ≤ CP * (kappa * ‖phi‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hD hCP.le
      _ = (CP * kappa) * ‖phi‖ ^ 2 := by ring
  by_contra hphi
  have hnorm : 0 < ‖phi‖ := norm_pos_iff.mpr hphi
  have hnorm_sq : 0 < ‖phi‖ ^ 2 := sq_pos_of_pos hnorm
  have hpositive : 0 < (1 - CP * kappa) * ‖phi‖ ^ 2 :=
    mul_pos (sub_pos.mpr hsmall) hnorm_sq
  nlinarith

end

end YangMills.RG
