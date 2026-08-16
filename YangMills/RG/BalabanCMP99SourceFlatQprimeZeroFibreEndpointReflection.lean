/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimeCrossFibreEndpointPhase
import YangMills.RG.BalabanCMP99SourceAliasReflectionStabilizedSolution

/-!
# Zero-coarse-fibre endpoint reflection

At zero coarse momentum the mass-zero central fine symbol vanishes, so the
nonzero quotient bridge cannot be used.  The correct replacement reindexes
the complete signed alias sum by the sealed half-open carrier reflection.
The endpoint phase is transported with its full physical alias period before
the stabilized transpose solution is changed to the column solution.

No actual cross-fibre carry is identified termwise with the reflection, and
no central quotient is cancelled.  This file stops at the literal CMP89
stabilized endpoint integrand.  Brillouin integration, regional `B0`, window
15, terminal fields and a `TermSource` inhabitant remain open.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The signed coarse base momentum at the literal zero Fourier mode is zero. -/
@[simp]
theorem cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_zero
    {d N' : ℕ} [NeZero N'] :
    cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
        (0 : FinBox d N') = 0 := by
  funext mu
  simp [cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum]

/-- Alias reflection moves the sign of the endpoint momentum to the physical
fine-lattice displacement.  The exceptional half-open endpoint is handled by
the sealed reflection and the full `2*pi*M` phase period. -/
theorem cmp99SourceAliasIndexOneReflection_endpointPhase_eq_negDisplacement
    {d M : ℕ} [NeZero M] (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d M 1) (u : Fin d → ℤ) :
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum (-z)
          (cmp99SourceAliasIndexOneReflection d M m).1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m.1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -u mu))) := by
  rcases cmp89Eq248EntireAliasMomentum_aliasIndexOneReflection z m with
    ⟨w, hw⟩
  rw [hw]
  calc
    _ = Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (-cmp89Eq248EntireAliasMomentum z m.1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) := by
      simpa only [Pi.neg_apply] using
        (exp_I_cmp89Eq251EntirePhase_add_int_aliasPeriods_physicalFine
          (N := M) (-cmp89Eq248EntireAliasMomentum z m.1) w u)
    _ = _ := by
      congr 2
      simp only [cmp89Eq251EntirePhase,
        cmp89Eq249PhysicalFineLatticeDisplacement, Pi.neg_apply]
      push_cast
      apply Finset.sum_congr rfl
      intro mu _
      ring

/-- One reflected zero-fibre transpose summand is exactly the corresponding
column summand at the opposite endpoint displacement. -/
theorem cmp99SourceAliasIndexOneReflection_transposeEndpointSummand_eq_column
    {d M : ℕ} [NeZero M] (mass a : ℝ) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d M 1) (u : Fin d → ℤ) :
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum (-z)
          (cmp99SourceAliasIndexOneReflection d M m).1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) *
      cmp89Eq249StabilizedAliasTransposeSolution d M 1 mass a (-z)
        (cmp99SourceAliasIndexOneReflection d M m) =
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m.1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -u mu))) *
      cmp89Eq249StabilizedAliasColumnSolution d M 1 mass a z m := by
  rw [cmp99SourceAliasIndexOneReflection_endpointPhase_eq_negDisplacement,
    cmp89Eq249StabilizedAliasTransposeSolution_neg_reflection_eq_column]

/-- The complete transpose endpoint sum at zero base momentum is the complete
column endpoint sum at the opposite physical displacement. -/
theorem sum_cmp99SourceZeroAliasTransposeEndpoint_eq_column
    {d M : ℕ} [NeZero M] (mass a : ℝ) (u : Fin d → ℤ) :
    (∑ m : CMP89Eq246AliasIndex d M 1,
        Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum (0 : Fin d → ℂ) m.1)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) *
        cmp89Eq249StabilizedAliasTransposeSolution d M 1 mass a 0 m) =
      ∑ m : CMP89Eq246AliasIndex d M 1,
        Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum (0 : Fin d → ℂ) m.1)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (fun mu => -u mu))) *
        cmp89Eq249StabilizedAliasColumnSolution d M 1 mass a 0 m := by
  let reflect := cmp99SourceAliasIndexOneReflection d M
  let row := fun m : CMP89Eq246AliasIndex d M 1 =>
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum (0 : Fin d → ℂ) m.1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) *
      cmp89Eq249StabilizedAliasTransposeSolution d M 1 mass a 0 m
  let column := fun m : CMP89Eq246AliasIndex d M 1 =>
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum (0 : Fin d → ℂ) m.1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -u mu))) *
      cmp89Eq249StabilizedAliasColumnSolution d M 1 mass a 0 m
  change (∑ m, row m) = ∑ m, column m
  calc
    (∑ m, row m) = ∑ m, row (reflect m) :=
      (Equiv.sum_comp reflect row).symm
    _ = ∑ m, column m := by
      apply Finset.sum_congr rfl
      intro m _
      simpa only [row, column, reflect, neg_zero] using
        (cmp99SourceAliasIndexOneReflection_transposeEndpointSummand_eq_column
          mass a (0 : Fin d → ℂ) m u)

/-- The complete physical zero-coarse-fibre transpose sum is exactly the
literal stabilized CMP89 column endpoint integrand at opposite displacement.
The central alias is never divided out. -/
theorem sum_cmp99SourceFlatPhysicalTransposeGreenEndpointSample_zero_eq_endpointIntegrand
    {d M N' : ℕ} [NeZero M] [NeZero N'] (mass a : ℝ)
    (x : FinBox d (M * N')) (y : FinBox d N') :
    (∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N'
          (0 : FinBox d N'),
        cmp99SourceFlatPhysicalTransposeGreenEndpointSample
          (0 : FinBox d N') mass a x y k) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d M 1 mass a
        (0 : Fin d → ℂ)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y mu)) := by
  let e := cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
    d M N' (0 : FinBox d N')
  let u := cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y
  let row := fun m : CMP89Eq246AliasIndex d M 1 =>
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum (0 : Fin d → ℂ) m.1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) *
      cmp89Eq249StabilizedAliasTransposeSolution d M 1 mass a 0 m
  calc
    (∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N'
          (0 : FinBox d N'),
        cmp99SourceFlatPhysicalTransposeGreenEndpointSample
          (0 : FinBox d N') mass a x y k) =
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N'
          (0 : FinBox d N'), row (e k) := by
      apply Finset.sum_congr rfl
      intro k _
      unfold cmp99SourceFlatPhysicalTransposeGreenEndpointSample
      simp only [cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_zero,
        row, u, e]
    _ = ∑ m : CMP89Eq246AliasIndex d M 1, row m := by
      exact Equiv.sum_comp e row
    _ = ∑ m : CMP89Eq246AliasIndex d M 1,
        Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum (0 : Fin d → ℂ) m.1)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (fun mu => -u mu))) *
        cmp89Eq249StabilizedAliasColumnSolution d M 1 mass a 0 m := by
      exact sum_cmp99SourceZeroAliasTransposeEndpoint_eq_column mass a u
    _ = cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d M 1 mass a
        (0 : Fin d → ℂ)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -u mu)) := by
      exact
        sum_exp_mul_cmp89Eq249StabilizedAliasColumnSolution_eq_endpointIntegrand
          d M 1 mass a (0 : Fin d → ℂ)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (fun mu => -u mu))

end

end YangMills.RG
