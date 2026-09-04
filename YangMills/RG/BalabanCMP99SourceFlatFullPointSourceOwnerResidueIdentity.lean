import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceOuterSynthesisDictionary
import YangMills.RG.BalabanCMP99SourceFlatFullPointSourcePhysicalEndpointReflection
import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceReversedOwnerCharacter
import YangMills.RG.BalabanCMP99FullGreenPhysicalFiniteGridAliasing
import YangMills.RG.BalabanCMP99PhysicalFullGreenOwnerResidueBound

/-!
# PRE-VALIDATION: generic full point-source affine residue identity

Source is present; the `.olean` is not materialized and this result is not
verified by the compiler. This source is not yet imported by the root aggregator.

F2 algebra before choosing a physical inverse: the literal internally solved
full point-source field equals Kfine^-4 times the reflected/swapped residue.
Kfine and N are independent. No generated/source coefficient identification,
Green reconstruction hypothesis, translation invariance or Q'^* is used.
The future source-flow consumer must use F1 by name at Kfine=L^(depth+1).
This is not a uniform physical B0 or window-15 attainment; counters unchanged.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Generic finite synthesis, reflection and aliasing with the full fine
normalization kept literal. The physical inverse is not an input. -/
theorem cmp99SourceFlatFullPointSourceSolution_eq_scaledOwnerResidue
    {Kfine N Nc : ℕ} [NeZero Kfine] [NeZero N] [NeZero Nc]
    {a rho : ℝ} (ha : 0 < a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (source target : FinBox 4 (Kfine * N))
    (v : SUNLieComplexCoord Nc) (A : Fin (Nc ^ 2 - 1)) :
    cmp99SourceFlatFullComplexPrecisionPointSourceSolution
        (d := 4) (M := Kfine) (N' := N) (Nc := Nc)
        0 a source v target A =
      ((((Kfine : ℂ) ^ 4)⁻¹) *
        cmp99PhysicalFullGreenUnscaledOwnerResidueSum
          (K := Kfine) (N := N) a source target) * v A := by
  let targetOwner : FinBox 4 N := blockSite Kfine N target
  let sourceOwner : FinBox 4 N := blockSite Kfine N source
  let targetDisp : Fin 4 → ℤ := fun mu =>
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
      Kfine target targetOwner mu
  let sourceDisp : Fin 4 → ℤ := fun mu =>
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
      Kfine source sourceOwner mu
  let r : CMP99FlatZModBox 4 N :=
    cmp99FinBoxZModEquiv 4 N sourceOwner -
      cmp99FinBoxZModEquiv 4 N targetOwner
  have hreflect : ∀ ell : FinBox 4 N,
      cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
          (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (fun mu => -targetDisp mu) (fun mu => -sourceDisp mu) =
        cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu) := by
    intro ell
    exact cmp99SourceFlatFullPointSourcePhysicalFineToFineGreenIntegrand_neg_swap
      ha hrho.le hamplitude hradius hdenWindow hpairWindow
      ell targetDisp sourceDisp
  have hchar : ∀ ell : FinBox 4 N,
      cmp99FlatFourierMode ell targetOwner *
          (cmp99FlatFourierMode ell sourceOwner)⁻¹ =
        cmp99FlatZModFourierCharacter
          (-(cmp99FinBoxZModEquiv 4 N ell)) r := by
    intro ell
    simpa [r] using
      cmp99FlatFourierMode_target_mul_source_inv_eq_reversedOwnerDifferenceCharacter
        ell targetOwner sourceOwner
  have hphysical : ∀ ell : FinBox 4 N,
      cmp89Eq246StabilizedFineToFineGreenIntegrand 4 Kfine 1 0 a
          (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((Kfine : ℝ)⁻¹)
            (fun mu => -targetDisp mu))
          (cmp89Eq249PhysicalFineLatticeDisplacement ((Kfine : ℝ)⁻¹)
            (fun mu => -sourceDisp mu)) =
        cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
          (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (fun mu => -targetDisp mu) (fun mu => -sourceDisp mu) := by
    intro ell
    simpa [cmp89Eq249FineLatticeSpacing] using
      (cmp89Eq246PhysicalFineToFineGreenIntegrand_eq Kfine 1 0 a
        (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (fun mu => -targetDisp mu) (fun mu => -sourceDisp mu)).symm
  let endpoint : FinBox 4 N → ℂ := fun ell =>
    cmp99FlatZModFourierCharacter
        (-(cmp99FinBoxZModEquiv 4 N ell)) r *
      cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu)
  have hbox :
      (∑ ell : FinBox 4 N, endpoint ell) =
        ∑ k : CMP99FlatZModBox 4 N,
          cmp99FlatZModFourierCharacter (-k) r *
            cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
              (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
                ((cmp99FinBoxZModEquiv 4 N).symm k))
              (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu) := by
    simpa [endpoint] using
      (Equiv.sum_comp (cmp99FinBoxZModEquiv 4 N)
        (fun k : CMP99FlatZModBox 4 N =>
          cmp99FlatZModFourierCharacter (-k) r *
            cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
              (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
                ((cmp99FinBoxZModEquiv 4 N).symm k))
              (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu)))
  have halias :=
    cmp99Flat_normalizedFiniteGridFullPhysicalGreenSample_eq_residueClass
      (K := Kfine) (N := N) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow
      (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu) r
  rw [cmp99SourceFlatFullComplexPrecisionPointSourceSolution_apply_eq_outerIntegrandSum
    (d := 4) (M := Kfine) (N' := N) (Nc := Nc) 0 a source target v A]
  dsimp only [targetOwner, sourceOwner, targetDisp, sourceDisp]
    at hphysical
  simp_rw [hphysical]
  have hterm : ∀ ell : FinBox 4 N,
      ((((((Kfine * N : ℕ) : ℂ) ^ 4)⁻¹) *
            cmp99FlatFourierMode ell targetOwner *
            (cmp99FlatFourierMode ell sourceOwner)⁻¹) *
          cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
            (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
            (fun mu => -targetDisp mu) (fun mu => -sourceDisp mu)) * v A =
        ((((((Kfine * N : ℕ) : ℂ) ^ 4)⁻¹) * endpoint ell) * v A) := by
    intro ell
    calc
      _ = ((((((Kfine * N : ℕ) : ℂ) ^ 4)⁻¹) *
            ((cmp99FlatFourierMode ell targetOwner *
              (cmp99FlatFourierMode ell sourceOwner)⁻¹) *
              cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
                (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
                (fun mu => -targetDisp mu) (fun mu => -sourceDisp mu))) * v A) := by
          ring
      _ = ((((((Kfine * N : ℕ) : ℂ) ^ 4)⁻¹) *
            (cmp99FlatZModFourierCharacter
                (-(cmp99FinBoxZModEquiv 4 N ell)) r *
              cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
                (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
                (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu))) * v A) := by
          rw [hchar ell, hreflect ell]
      _ = _ := by rfl
  dsimp only [targetOwner, sourceOwner, targetDisp, sourceDisp]
    at hterm
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hbox]
  have hscale : ((((Kfine * N : ℕ) : ℂ) ^ 4)⁻¹) =
      (((Kfine : ℂ) ^ 4)⁻¹) * (((N : ℂ) ^ 4)⁻¹) := by
    push_cast
    rw [mul_pow, mul_inv_rev]
    ring
  rw [hscale]
  calc
    _ = (((Kfine : ℂ) ^ 4)⁻¹) *
          ((((N : ℂ) ^ 4)⁻¹) *
            ∑ k : CMP99FlatZModBox 4 N,
              cmp99FlatZModFourierCharacter (-k) r *
                cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
                  (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
                    ((cmp99FinBoxZModEquiv 4 N).symm k))
                  (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu)) * v A := by
            ring
    _ = _ := by
      rw [halias]
      unfold cmp99PhysicalFullGreenUnscaledOwnerResidueSum
      dsimp [targetOwner, sourceOwner, targetDisp, sourceDisp, r]

end

end YangMills.RG
