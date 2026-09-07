import YangMills.RG.BalabanCMP89CenteredTorusGreenCoefficientPhase

/-!
# PRE-VALIDATION: alias-independent phases for a common block translation

Source present; .olean not materialized; result not compiler-verified.
Physical spacing is 1/M and the fine-site shift is M*n, not n.
The base momentum is complex. This imports only existing phase machinery,
not the pending full-solution scalar draft. It proves no Green covariance.
-/

namespace YangMills.RG
noncomputable section

theorem neumannAliasTargetPhase_blockShift
    {d M : ℕ} (hM : 0 < M) (z : Fin d → ℂ)
    (alias site shift : Fin d → ℤ) :
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z alias)
      (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
        (fun mu => site mu + (M : ℤ) * shift mu))) =
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z alias)
      (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) site)) *
      Complex.exp (Complex.I * ∑ mu, z mu * (shift mu : ℂ)) := by
  rw [cmp89Eq251EntirePhase_physicalFine_affineResidue hM,
    mul_add, Complex.exp_add]
  congr 1
  simpa [cmp89Eq251EntirePhase,
    cmp89Eq249PhysicalFineLatticeDisplacement] using
    exp_I_cmp89Eq251EntireAliasPhase_latticeDisplacement z alias shift

theorem neumannAliasSourcePhase_blockShift
    {d M : ℕ} (hM : 0 < M) (z : Fin d → ℂ)
    (alias site shift : Fin d → ℤ) :
    Complex.exp (-Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z alias)
      (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
        (fun mu => site mu + (M : ℤ) * shift mu))) =
    Complex.exp (-Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z alias)
      (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) site)) *
      Complex.exp (-Complex.I * ∑ mu, z mu * (shift mu : ℂ)) := by
  have h := congrArg (fun c : ℂ => c⁻¹)
    (neumannAliasTargetPhase_blockShift hM z alias site shift)
  simpa [neg_mul, Complex.exp_neg, mul_comm] using h

theorem neumannCommonBlockPhase_cancel {d : ℕ}
    (z : Fin d → ℂ) (shift : Fin d → ℤ) :
    Complex.exp (Complex.I * ∑ mu, z mu * (shift mu : ℂ)) *
      Complex.exp (-Complex.I * ∑ mu, z mu * (shift mu : ℂ)) = 1 := by
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 1 <;> ring

#print axioms neumannAliasTargetPhase_blockShift
#print axioms neumannAliasSourcePhase_blockShift
#print axioms neumannCommonBlockPhase_cancel

end
end YangMills.RG
