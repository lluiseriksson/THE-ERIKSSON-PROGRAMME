import YangMills.RG.BalabanCMP99SourceGaugePrecision
import YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann
import YangMills.RG.BalabanCMP99SourceEq395LocalInverse

/-!
PRE-VALIDATION: source present; `.olean` not yet materialized and the result
has not yet been verified by the compiler or axiom oracle.

# Dirichlet compression of the canonical ambient `Qprime` extension

This is the algebraic half of the C6d source dictionary.  An active terminal
average is extended to the ambient field only by first restricting the input
to the active carrier.  Compressing the resulting ambient adjoint square
recovers the original active adjoint square exactly.

This algebraic extension is not the physical full-carrier source `Qprime` and
does not by itself inherit ambient coercivity.  A later source dictionary must
identify the restriction of the complete generated tower with the active C6d
terminal average before this lemma can feed Eq. (3.42).
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {M Q : ℕ} [NeZero M] [NeZero Q]
variable {g F : Type*}
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Canonical ambient action of an active terminal average: discard the
complement and apply the same active operator. -/
noncomputable def cmp99RegionalAmbientRestrictedQprime
    (Omega : ActiveGaugeRegion 4 (M * (2 * Q)))
    (Qprime : ActiveGaugeZeroCochain Omega g →L[ℝ] F) :
    GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ] F :=
  Qprime.comp (restrictZeroCLM Omega)

/-- Dirichlet compression commutes exactly with adding the canonical
ambient realization of `a Qprime.adjoint Qprime`.

The adjoint orientation is proved through the named restriction/extension
partial-isometry identities; it is not inferred from matching types. -/
theorem cmp99RegionalDirichletPrecision_sourceGaugePrecision_eq
    (Omega : ActiveGaugeRegion 4 (M * (2 * Q)))
    (Delta : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    (Qprime : ActiveGaugeZeroCochain Omega g →L[ℝ] F)
    (a : ℝ) :
    cmp99RegionalDirichletPrecision Omega
        (cmp99SourceGaugePrecision Delta
          (cmp99RegionalAmbientRestrictedQprime Omega Qprime) a) =
      cmp99SourceGaugePrecision
        (cmp99RegionalDirichletPrecision Omega Delta) Qprime a := by
  let E := extendZeroZeroCLM (𝔤 := g) Omega
  let R := restrictZeroCLM (𝔤 := g) Omega
  have hRE : R.comp E =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain Omega g) :=
    activeGaugeRegion_restrictZero_comp_extendZero Omega
  have hR : R = E.adjoint :=
    cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint Omega
  have hRadj : R.adjoint = E := by
    rw [hR, ContinuousLinearMap.adjoint_adjoint]
  have hRE_apply (phi : ActiveGaugeZeroCochain Omega g) : R (E phi) = phi := by
    have h := congrArg
      (fun T : ActiveGaugeZeroCochain Omega g →L[ℝ]
        ActiveGaugeZeroCochain Omega g => T phi) hRE
    simpa using h
  apply ContinuousLinearMap.ext
  intro phi
  simp only [cmp99RegionalDirichletPrecision, cmp99SourceGaugePrecision,
    cmp99RegionalAmbientRestrictedQprime, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.adjoint_comp]
  rw [hRadj]
  change R (Delta (E phi) + a • E (Qprime.adjoint (Qprime phi))) =
    R (Delta (E phi)) + a • Qprime.adjoint (Qprime phi)
  rw [map_add, map_smul, hRE_apply]

end

end YangMills.RG
