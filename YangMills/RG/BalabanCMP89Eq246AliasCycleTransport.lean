import YangMills.RG.BalabanCMP89Eq246FinePointSourceFibreGreen
import YangMills.RG.BalabanCMP89Eq248AliasMomentumCycle
import YangMills.RG.BalabanCMP89Eq245EntireAveragePeriodicity
import YangMills.RG.BalabanCMP89Eq245EntireScaledLaplacianPeriodicity
import YangMills.RG.BalabanCMP89Eq251FineLatticePhasePeriodicity

/-!
# PRE-VALIDATION: source-faithful alias-cycle transport for CMP89 (2.46)

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

These are the pointwise covariance identities needed before transporting the
complete finite alias system.  Every identity is derived from the centered
alias permutation and the literal `2*pi*N` periods of the printed factors.
No periodicity of the solved Green or of the complete integrand is assumed.
-/

namespace YangMills.RG

noncomputable section

private theorem cmp89Eq246AliasCount_pos
    (L j : ℕ) [NeZero L] : 0 < L ^ j :=
  pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j

/-- The diagonal fine symbol at the shifted coarse momentum is the diagonal
symbol at the cycled centered alias. -/
theorem cmp89Eq246EntireAliasFineSymbol_physicalShift_eq_cycle
    (d L j : ℕ) [NeZero L] (mass : ℝ) (mu : Fin d)
    (z : Fin d → ℂ) (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246EntireAliasFineSymbol d L j mass
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m =
      cmp89Eq246EntireAliasFineSymbol d L j mass z
        (cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
          (cmp89Eq246AliasCount_pos L j) mu m) := by
  unfold cmp89Eq246EntireAliasFineSymbol
  apply cmp89Eq248AliasFactor_physicalShift_eq_cycle
    (cmp89Eq246AliasCount_pos L j) mu z
  intro q
  simpa only [Nat.cast_pow] using
    (cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
      (cmp89Eq246AliasCount_pos L j) mass mu q)

/-- The averaging column transports through the same centered-alias cycle. -/
theorem cmp89Eq246EntireAliasAverageColumn_physicalShift_eq_cycle
    (d L j : ℕ) [NeZero L] (mu : Fin d)
    (z : Fin d → ℂ) (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246EntireAliasAverageColumn d L j
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m =
      cmp89Eq246EntireAliasAverageColumn d L j z
        (cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
          (cmp89Eq246AliasCount_pos L j) mu m) := by
  unfold cmp89Eq246EntireAliasAverageColumn
  apply cmp89Eq248AliasFactor_physicalShift_eq_cycle
    (cmp89Eq246AliasCount_pos L j) mu z
  intro q
  exact cmp89Eq245EntireAverageAmplitude_coordinateAliasPeriodShift
    (cmp89Eq246AliasCount_pos L j) mu q

/-- The holomorphic opposite-momentum row transports through the same
centered-alias cycle. -/
theorem cmp89Eq246EntireAliasAverageRow_physicalShift_eq_cycle
    (d L j : ℕ) [NeZero L] (mu : Fin d)
    (z : Fin d → ℂ) (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246EntireAliasAverageRow d L j
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m =
      cmp89Eq246EntireAliasAverageRow d L j z
        (cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
          (cmp89Eq246AliasCount_pos L j) mu m) := by
  unfold cmp89Eq246EntireAliasAverageRow
  apply cmp89Eq248AliasFactor_physicalShift_eq_cycle
    (cmp89Eq246AliasCount_pos L j) mu z
  intro q
  exact cmp89Eq245EntireAverageAmplitude_neg_coordinateAliasPeriodShift
    (cmp89Eq246AliasCount_pos L j) mu q

/-- A normalized physical fine-point source transports through the alias
cycle.  The wrap phase is an integer multiple of `2*pi`. -/
theorem cmp89Eq246FinePointSourceAliasVector_physicalShift_eq_cycle
    (d L j : ℕ) [NeZero L] (mu : Fin d)
    (z : Fin d → ℂ) (source : Fin d → ℤ)
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246FinePointSourceAliasVector d L j
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) source) m =
      cmp89Eq246FinePointSourceAliasVector d L j z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) source)
        (cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
          (cmp89Eq246AliasCount_pos L j) mu m) := by
  unfold cmp89Eq246FinePointSourceAliasVector
  apply cmp89Eq248AliasFactor_physicalShift_eq_cycle
    (cmp89Eq246AliasCount_pos L j) mu z
  intro q
  have h :=
    exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift_physicalFine
      (L ^ j) mu q (fun k => -source k)
  simpa [cmp89Eq249PhysicalFineLatticeDisplacement,
    cmp89Eq251EntirePhase] using h

/-- The inverse-transform target phase transports through the alias cycle. -/
theorem exp_I_cmp89Eq246TargetPhase_physicalShift_eq_cycle
    (d L j : ℕ) [NeZero L] (mu : Fin d)
    (z : Fin d → ℂ) (target : Fin d → ℤ)
    (m : CMP89Eq246AliasIndex d L j) :
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m.1)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) target)) =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z
          (cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
            (cmp89Eq246AliasCount_pos L j) mu m).1)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) target)) := by
  apply cmp89Eq248AliasFactor_physicalShift_eq_cycle
    (cmp89Eq246AliasCount_pos L j) mu z
  intro q
  exact exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift_physicalFine
    (L ^ j) mu q target

end

end YangMills.RG
