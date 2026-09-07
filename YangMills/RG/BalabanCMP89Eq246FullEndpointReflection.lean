import YangMills.RG.BalabanCMP89Eq246AliasReflectionTransposeFullSolution
import YangMills.RG.BalabanCMP89Eq246FinePointSourceTargetDuality
import YangMills.RG.BalabanCMP89Eq246FullSolutionDomain
import YangMills.RG.BalabanCMP89Eq246StabilizedAliasFullTransposePairing
import YangMills.RG.BalabanCMP99SourceAliasReflectionInvolutive
import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceCharacterDictionary

/-!
# Full endpoint reflection below CMP89 (2.46)

This module composes the literal direct/transpose pairing, the
actual half-open alias reflection and the fine-point-source phase dictionary.
It accepts only the two already named complete solver domains at `z` and
`-z`; no Green symmetry or solved inverse is an input.
-/

namespace YangMills.RG

noncomputable section

/-- At depth one, simultaneous momentum and endpoint reflection exchanges
the two physical fine endpoints. -/
theorem cmp89Eq246StabilizedDepthOnePhysicalEndpointReflection
    (d M : ℕ) [NeZero M] (mass a : ℝ) (z : Fin d → ℂ)
    (target source : Fin d → ℤ)
    (hz : CMP89Eq246FullSolutionDomain d M 1 mass a z)
    (hneg : CMP89Eq246FullSolutionDomain d M 1 mass a (-z)) :
    cmp89Eq246StabilizedFineToFineGreenIntegrand d M 1 mass a (-z)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -target mu))
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -source mu)) =
      cmp89Eq246StabilizedFineToFineGreenIntegrand d M 1 mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -source mu))
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -target mu)) := by
  classical
  let xi : ℝ := (M : ℝ)⁻¹
  let reflect := cmp99SourceAliasIndexOneReflection d M
  let leftSource : CMP89Eq246AliasIndex d M 1 → ℂ :=
    cmp89Eq246FinePointSourceAliasVector d M 1 (-z)
      (cmp89Eq249PhysicalFineLatticeDisplacement xi
        (fun mu => -source mu))
  let leftTarget : CMP89Eq246AliasIndex d M 1 → ℂ :=
    cmp89Eq246FinePointSourceAliasVector d M 1 (-z)
      (cmp89Eq249PhysicalFineLatticeDisplacement xi target)
  let rightSource : CMP89Eq246AliasIndex d M 1 → ℂ :=
    cmp89Eq246FinePointSourceAliasVector d M 1 z
      (cmp89Eq249PhysicalFineLatticeDisplacement xi
        (fun mu => -target mu))
  let rightTarget : CMP89Eq246AliasIndex d M 1 → ℂ :=
    cmp89Eq246FinePointSourceAliasVector d M 1 z
      (cmp89Eq249PhysicalFineLatticeDisplacement xi source)
  have hcolumnNeg :
      cmp89Eq246EntireAliasAverageColumn d M 1 (-z)
          (cmp89Eq249CentralAliasIndex d M 1) ≠ 0 := by
    have hcolumnAtReflection :
        cmp89Eq246EntireAliasAverageColumn d M 1 (-z)
            (reflect (cmp89Eq249CentralAliasIndex d M 1)) ≠ 0 := by
      rw [cmp89Eq246EntireAliasAverageColumn_neg_reflection_eq_row
        (d := d) (M := M) z (cmp89Eq249CentralAliasIndex d M 1)]
      exact hz.row
    simpa only [reflect, cmp99SourceAliasIndexOneReflection_central] using
      hcolumnAtReflection
  have hleftPhase (m : CMP89Eq246AliasIndex d M 1) :
      Complex.exp
          (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum (-z) m.1)
            (cmp89Eq249PhysicalFineLatticeDisplacement xi
              (fun mu => -target mu))) =
        leftTarget m := by
    symm
    simpa only [leftTarget, xi, neg_neg] using
      (cmp89Eq246FinePointSourceAliasVector_negPhysicalEndpoint_eq_targetPhase
        xi (-z) m (fun mu => -target mu))
  have hrightPhase (m : CMP89Eq246AliasIndex d M 1) :
      Complex.exp
          (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m.1)
            (cmp89Eq249PhysicalFineLatticeDisplacement xi
              (fun mu => -source mu))) =
        rightTarget m := by
    symm
    simpa only [rightTarget, xi, neg_neg] using
      (cmp89Eq246FinePointSourceAliasVector_negPhysicalEndpoint_eq_targetPhase
        xi z m (fun mu => -source mu))
  have hleftSourceReflect (m : CMP89Eq246AliasIndex d M 1) :
      leftSource (reflect m) = rightTarget m := by
    have h := congrFun
      (cmp89Eq246FinePointSourceAliasVector_comp_reflection_eq_neg
        (d := d) (M := M) (-z) (fun mu => -source mu)) m
    simpa only [leftSource, rightTarget, reflect, xi, neg_neg] using h
  have hreflectSymm (m : CMP89Eq246AliasIndex d M 1) :
      reflect.symm m = reflect m := by
    apply reflect.injective
    simp only [Equiv.apply_symm_apply, reflect,
      cmp99SourceAliasIndexOneReflection_apply_apply]
  have htargetReflection :
      cmp89Eq246AliasReflectionSource d M rightSource = leftTarget := by
    funext m
    change rightSource (reflect.symm m) = leftTarget m
    rw [hreflectSymm m]
    have h := congrFun
      (cmp89Eq246FinePointSourceAliasVector_comp_reflection_eq_neg
        (d := d) (M := M) z (fun mu => -target mu)) m
    simpa only [rightSource, leftTarget, reflect, xi, neg_neg] using h
  have hsolutionReflect (m : CMP89Eq246AliasIndex d M 1) :
      cmp89Eq246StabilizedAliasTransposeFullSolution
          d M 1 mass a (-z) leftTarget (reflect m) =
        cmp89Eq246StabilizedAliasFullSolution
          d M 1 mass a z rightSource m := by
    rw [← htargetReflection]
    exact cmp89Eq246StabilizedAliasTransposeFullSolution_neg_reflection
      d M mass a z rightSource m
  have hpair :
      (∑ m, leftTarget m *
          cmp89Eq246StabilizedAliasFullSolution
            d M 1 mass a (-z) leftSource m) =
        ∑ m, leftSource m *
          cmp89Eq246StabilizedAliasTransposeFullSolution
            d M 1 mass a (-z) leftTarget m := by
    exact cmp89Eq246StabilizedAliasFullSolution_transpose_pairing
      d M 1 mass a (-z) leftSource leftTarget hneg.fine hneg.stabilized
        hneg.row hcolumnNeg
  unfold cmp89Eq246StabilizedFineToFineGreenIntegrand
  change
    (∑ m, Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum (-z) m.1)
          (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (fun mu => -target mu))) *
        cmp89Eq246StabilizedAliasFullSolution
          d M 1 mass a (-z) leftSource m) =
      ∑ m, Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m.1)
          (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (fun mu => -source mu))) *
        cmp89Eq246StabilizedAliasFullSolution
          d M 1 mass a z rightSource m
  calc
    _ = ∑ m, leftTarget m *
        cmp89Eq246StabilizedAliasFullSolution
          d M 1 mass a (-z) leftSource m := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hleftPhase]
    _ = ∑ m, leftSource m *
        cmp89Eq246StabilizedAliasTransposeFullSolution
          d M 1 mass a (-z) leftTarget m := hpair
    _ = ∑ m, leftSource (reflect m) *
        cmp89Eq246StabilizedAliasTransposeFullSolution
          d M 1 mass a (-z) leftTarget (reflect m) := by
      exact
        (Equiv.sum_comp reflect (fun m => leftSource m *
          cmp89Eq246StabilizedAliasTransposeFullSolution
            d M 1 mass a (-z) leftTarget m)).symm
    _ = ∑ m, rightTarget m *
        cmp89Eq246StabilizedAliasFullSolution
          d M 1 mass a z rightSource m := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hleftSourceReflect, hsolutionReflect]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hrightPhase]

/-- Physical-wrapper form consumed by the literal finite-grid aliasing
theorem.  The only extra reduction is the printed depth-one spacing
`(M ^ 1)^{-1} = M^{-1}`; no periodic endpoint identification is used. -/
theorem cmp89Eq246PhysicalFineToFineGreenIntegrand_neg_swap
    (M : ℕ) [NeZero M] (mass a : ℝ) (z : Fin 4 → ℂ)
    (target source : Fin 4 → ℤ)
    (hz : CMP89Eq246FullSolutionDomain 4 M 1 mass a z)
    (hneg : CMP89Eq246FullSolutionDomain 4 M 1 mass a (-z)) :
    cmp89Eq246PhysicalFineToFineGreenIntegrand M 1 mass a (-z)
        (fun mu => -target mu) (fun mu => -source mu) =
      cmp89Eq246PhysicalFineToFineGreenIntegrand M 1 mass a z
        (fun mu => -source mu) (fun mu => -target mu) := by
  rw [cmp89Eq246PhysicalFineToFineGreenIntegrand_eq,
    cmp89Eq246PhysicalFineToFineGreenIntegrand_eq]
  simpa [cmp89Eq249FineLatticeSpacing] using
    (cmp89Eq246StabilizedDepthOnePhysicalEndpointReflection
      4 M mass a z target source hz hneg)

end

end YangMills.RG
