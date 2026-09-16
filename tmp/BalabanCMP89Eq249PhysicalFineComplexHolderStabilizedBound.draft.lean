/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

/-
PRE-VALIDATION IMPORT CONTRACT.

The first two imports name intended promoted H2d1/H2d2 modules.  They do not
exist in the tracked tree yet, so this integration draft is deliberately not
a compilable target until those bricks have been materialized.
-/
import YangMills.RG.BalabanCMP89Eq249PhysicalFineComplexHolderPhasedNoncentralSum
import YangMills.RG.BalabanCMP89Eq249PhysicalFineComplexHolderCentralBranch
import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexFloorMassUniform

/-!
# PRE-VALIDATION: physical fine Holder stabilized strip bound

This H2d3 source is a static draft.  Its `.olean` has not been materialized
and none of its declarations has been compiler-verified.

It first identifies the literal stabilized numerator as

`central Holder branch + central fine symbol * noncentral Holder sum`

and only then applies the single common stabilized reciprocal.  Both branches
carry the same exact signed transport decay.  Their budgets remain separate
inside the final explicit constant, so no alias sum is used for the central
term and the denominator is paid exactly once.

This is a pointwise bound on the signed contour.  It does not prove equality
of the real and displaced integrals, identify the signed `ell^1` length with
the source/owner metric, construct regional `B0`, attain window 15, discharge
a terminal field or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit H2d3 constant.  The zero/nonzero alias split and the one common
stabilized reciprocal remain visible. -/
def cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft
    (a rho alpha : ℝ) : ℝ :=
  (cmp89Eq249ComplexPhysicalFineHolderCentralBranchBound_draft rho alpha +
      cmp89Eq251CentralFineSymbolStripUpperBound rho *
        cmp89Eq249ComplexHolderNoncentralAliasSumBound_draft rho alpha) *
    cmp89Eq249CentralStabilizedComplexReciprocalBound a rho

/-- Exact H2d3 numerator split at physical fine spacing.  No alias phase is
factored out of the noncentral finite sum. -/
theorem cmp89Eq251ComplexStabilizedNumerator_eq_physicalFineHolderBranches_draft
    {L j : ℕ} {mass alpha : ℝ} (z : Fin 4 → ℂ) (mu : Fin 4)
    (holderU : Fin 4 → ℤ) (transportDisplacement : Fin 4 → ℝ) :
    cmp89Eq251ComplexStabilizedNumerator 4 L j mass alpha z mu
        (cmp89Eq249PhysicalFineLatticeDisplacement (((L : ℝ) ^ j)⁻¹) holderU)
        transportDisplacement =
      cmp89Eq249ComplexPhysicalFineHolderCentralBranch_draft
          L j alpha z mu holderU transportDisplacement +
        cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
          cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_draft
            L j mass alpha z mu holderU transportDisplacement := by
  let aliases := (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
    (cmp89Eq249ZeroAlias 4)
  rw [cmp89Eq251ComplexStabilizedNumerator,
    cmp89Eq251ComplexBareAliasNumerator_zero_eq_physicalFineHolderCentralBranch_draft,
    cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_draft]
  congr 2
  apply Finset.sum_congr rfl
  intro m hm
  rw [cmp89Eq251ComplexBareAliasNumerator]
  ring

/-- H2d3: the complete literal stabilized Holder integrand is bounded on one
signed transport contour by its exact decay times the explicit common
central/noncentral constant. -/
theorem norm_cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolder_signedContour_le_draft
    {L j : ℕ} [NeZero L] {mass a rho alpha : ℝ}
    (ha : 0 ≤ a) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (halphaStrict : alpha < 1) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {holderU : Fin 4 → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holderU)
    (transportDisplacement : Fin 4 → ℝ)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) :
    ‖cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (cmp89Eq251SignedContourMomentum rho p transportDisplacement) mu
        (cmp89Eq249PhysicalFineLatticeDisplacement (((L : ℝ) ^ j)⁻¹) holderU)
        transportDisplacement‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 transportDisplacement)) *
        cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft
          a rho alpha := by
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p transportDisplacement
  let decay : ℝ :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 transportDisplacement))
  let centralBound :=
    cmp89Eq249ComplexPhysicalFineHolderCentralBranchBound_draft rho alpha
  let noncentralBound :=
    cmp89Eq249ComplexHolderNoncentralAliasSumBound_draft rho alpha
  let fineBound := cmp89Eq251CentralFineSymbolStripUpperBound rho
  let reciprocal :=
    cmp89Eq249CentralStabilizedComplexReciprocalBound a rho
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p transportDisplacement nu
  have hcentral :
      ‖cmp89Eq249ComplexPhysicalFineHolderCentralBranch_draft
          L j alpha z mu holderU transportDisplacement‖ ≤
        decay * centralBound := by
    simpa only [z, decay, centralBound] using
      (norm_cmp89Eq249ComplexPhysicalFineHolderCentralBranch_signedContour_le_draft
        (L := L) (j := j) halpha0 halpha1 hrho hp hunit
        transportDisplacement mu)
  have hnoncentral :
      ‖cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_draft
          L j mass alpha z mu holderU transportDisplacement‖ ≤
        decay * noncentralBound := by
    simpa only [z, decay, noncentralBound] using
      (norm_cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_signedContour_le_draft
        (L := L) (j := j) (mass := mass) halpha0 halpha1 halphaStrict
        hrho hradius hp hunit transportDisplacement hamplitude mu)
  have hfine :
      ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z‖ ≤ fineBound := by
    simpa only [fineBound] using
      (norm_cmp89Eq249CentralEntireFineSymbol_le_stripUpperBound
        (L := L) (j := j) hmass hrho hp hreal himag)
  have hreciprocal :
      ‖(cmp89Eq249CentralStabilizedAliasDenominator
          4 L j mass a z)⁻¹‖ ≤ reciprocal := by
    simpa only [reciprocal] using
      (norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le_massUniform
        (L := L) (j := j) (mass := mass) ha hrho hradius hmass hwindow
        hp hreal himag hamplitude)
  have hdecay : 0 ≤ decay := (Real.exp_pos _).le
  have hcentralBound : 0 ≤ centralBound := by
    dsimp [centralBound,
      cmp89Eq249ComplexPhysicalFineHolderCentralBranchBound_draft,
      cmp89Eq251ComplexCentralEndpointAmplitudeBound]
    positivity
  have hnoncentralBound : 0 ≤ noncentralBound := by
    dsimp [noncentralBound,
      cmp89Eq249ComplexHolderNoncentralAliasSumBound_draft,
      cmp89Eq249ComplexHolderNoncentralRadialConstant_draft,
      cmp89Eq251ComplexNoncentralEndpointRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hfineBound : 0 ≤ fineBound := by
    dsimp [fineBound, cmp89Eq251CentralFineSymbolStripUpperBound,
      cmp89Eq249CentralFineSymbolVerticalBound,
      cmp89Eq249CentralFineSymbolRealBound]
    positivity
  have hreciprocalNonneg : 0 ≤ reciprocal := by
    dsimp [reciprocal, cmp89Eq249CentralStabilizedComplexReciprocalBound]
    positivity
  have hnoncentralProduct :
      ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
          cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_draft
            L j mass alpha z mu holderU transportDisplacement‖ ≤
        decay * (fineBound * noncentralBound) := by
    rw [norm_mul]
    calc
      ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z‖ *
          ‖cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_draft
            L j mass alpha z mu holderU transportDisplacement‖ ≤
        fineBound * (decay * noncentralBound) := by gcongr
      _ = decay * (fineBound * noncentralBound) := by ring
  have hnumerator :
      ‖cmp89Eq251ComplexStabilizedNumerator 4 L j mass alpha z mu
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L : ℝ) ^ j)⁻¹) holderU)
          transportDisplacement‖ ≤
        decay * (centralBound + fineBound * noncentralBound) := by
    rw [cmp89Eq251ComplexStabilizedNumerator_eq_physicalFineHolderBranches_draft]
    calc
      ‖cmp89Eq249ComplexPhysicalFineHolderCentralBranch_draft
            L j alpha z mu holderU transportDisplacement +
          cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
            cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_draft
              L j mass alpha z mu holderU transportDisplacement‖ ≤
        ‖cmp89Eq249ComplexPhysicalFineHolderCentralBranch_draft
            L j alpha z mu holderU transportDisplacement‖ +
          ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
            cmp89Eq249ComplexPhysicalFineHolderPhasedNoncentralSum_draft
              L j mass alpha z mu holderU transportDisplacement‖ :=
        norm_add_le _ _
      _ ≤ decay * centralBound + decay * (fineBound * noncentralBound) :=
        add_le_add hcentral hnoncentralProduct
      _ = decay * (centralBound + fineBound * noncentralBound) := by ring
  rw [cmp89Eq251ComplexStabilizedIntegrand, div_eq_mul_inv, norm_mul,
    cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft]
  change _ ≤ decay * ((centralBound + fineBound * noncentralBound) * reciprocal)
  calc
    ‖cmp89Eq251ComplexStabilizedNumerator 4 L j mass alpha z mu
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L : ℝ) ^ j)⁻¹) holderU)
          transportDisplacement‖ *
        ‖(cmp89Eq249CentralStabilizedAliasDenominator
          4 L j mass a z)⁻¹‖ ≤
      (decay * (centralBound + fineBound * noncentralBound)) * reciprocal := by
        gcongr
    _ = decay * ((centralBound + fineBound * noncentralBound) * reciprocal) :=
      by ring

end

end YangMills.RG
