/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Pointwise mass-uniform Green bound below CMP89 (2.48)--(2.49).  This scratch
file is intentionally not imported by `YangMillsCore`. -/

import YangMills.RG.BalabanCMP89Eq248GreenMassUniformHolomorphy
import YangMills.RG.BalabanCMP89Eq251ComplexNoncentralEndpointQuotientBound
import YangMills.RG.BalabanCMP89Eq251SignedContourPhase
import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointCentralFineUpper

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- Radial constant for one Green quotient before the `alpha = -1`
redistribution.  Unlike the differentiated endpoint, there is no scaled
difference to cancel one inverse momentum power. -/
def cmp89Eq248ComplexNoncentralGreenRadialConstant_draft (rho : ℝ) : ℝ :=
  2 * (3 * Real.pi) ^ 2 *
    cmp89Eq245EntireAverageAliasStripConstant rho ^ 4

/-- Product-weight constant for one noncentral Green quotient. -/
def cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft (rho : ℝ) : ℝ :=
  cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho *
    3 ^ (1 - (-1 : ℝ))

/-- One noncentral Green quotient retains two inverse radial powers and one
reciprocal-alias product weight. -/
theorem norm_cmp89Eq248ComplexNoncentralGreenQuotient_le_radialWeight_draft
    {N : ℕ} (hN : 0 < N) {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 N) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAverageAmplitude 4 N
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
          (cmp89Eq248EntireAliasMomentum z m)‖ ≤
      cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho *
        (cmp89Eq251EuclideanNorm
            (fun nu => p nu + 2 * Real.pi * (m nu : ℝ)) ^
              ((-1 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by
  let q : Fin 4 → ℝ :=
    fun nu => p nu + 2 * Real.pi * (m nu : ℝ)
  let aliasZ : Fin 4 → ℂ := cmp89Eq248EntireAliasMomentum z m
  have haliasReal : ∀ nu, (aliasZ nu).re = q nu := by
    intro nu
    simp [aliasZ, q, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift, hreal nu]
  have haliasImag : ∀ nu, |(aliasZ nu).im| ≤ rho := by
    intro nu
    simpa [aliasZ, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift] using himag nu
  have havg :
      ‖cmp89Eq245EntireAverageAmplitude 4 N aliasZ‖ ≤
        cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
          cmp89Eq251MultidimensionalAliasWeight 1 m := by
    exact norm_cmp89Eq245EntireAverageAmplitude_scaled_alias_le
      hN hm hrho hp haliasReal haliasImag hamplitude
  have hden :
      ((1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q) / 2 ≤
        ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 (N : ℝ)⁻¹ mass aliasZ‖ := by
    simpa only [q] using
      half_momentum_gap_le_norm_cmp89Eq245EntireScaledLaplacianSymbol_of_uniformRadius
        hN hrho hradius hm hm0 hp haliasReal haliasImag
  have hqNorm : 0 < cmp89Eq251EuclideanNorm q :=
    Real.pi_pos.trans_le (pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp)
  have hqSquare : 0 < cmp89Eq251MomentumSquare q := by
    rw [← sq_cmp89Eq251EuclideanNorm]
    positivity
  have hgap :
      0 < ((1 / (3 * Real.pi)) ^ 2 *
        cmp89Eq251MomentumSquare q) / 2 := by positivity
  have hdenInv :
      ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 (N : ℝ)⁻¹ mass aliasZ‖⁻¹ ≤
        (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hgap hden
  have hpower :
      cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) =
        (cmp89Eq251MomentumSquare q)⁻¹ := by
    rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
      Real.rpow_neg hqNorm.le, Real.rpow_two,
      sq_cmp89Eq251EuclideanNorm]
  have hgapInv :
      (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ =
        2 * (3 * Real.pi) ^ 2 *
          (cmp89Eq251MomentumSquare q)⁻¹ := by
    field_simp [Real.pi_ne_zero, ne_of_gt hqSquare]
  rw [show cmp89Eq248EntireAliasMomentum z m = aliasZ by rfl,
    norm_div, div_eq_mul_inv]
  calc
    ‖cmp89Eq245EntireAverageAmplitude 4 N aliasZ‖ *
        ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 (N : ℝ)⁻¹ mass aliasZ‖⁻¹ ≤
      (cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
          cmp89Eq251MultidimensionalAliasWeight 1 m) *
        (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ := by
      gcongr
    _ = cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho *
        (cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by
      rw [hgapInv, hpower,
        cmp89Eq248ComplexNoncentralGreenRadialConstant_draft]
      ring

/-- The Green quotient uses the strictly summable `alpha = -1` source
weight. -/
theorem norm_cmp89Eq248ComplexNoncentralGreenQuotient_le_sourceWeight_draft
    {N : ℕ} (hN : 0 < N) {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 N) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAverageAmplitude 4 N
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
          (cmp89Eq248EntireAliasMomentum z m)‖ ≤
      cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
  let q : Fin 4 → ℝ :=
    fun nu => p nu + 2 * Real.pi * (m nu : ℝ)
  have hradial :=
    norm_cmp89Eq248ComplexNoncentralGreenQuotient_le_radialWeight_draft
      (mass := mass) hN hrho hradius hm hm0 hp hreal himag hamplitude
  have hredistribute :
      cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m ≤
        3 ^ (1 - (-1 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
    exact cmp89Eq251EuclideanNorm_rpow_mul_aliasWeight_le_sourceWeight
      (d := 4) (alpha := (-1 : ℝ)) (by norm_num) (by norm_num) hm0 hp
  have hconstant :
      0 ≤ cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho := by
    rw [cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  calc
    _ ≤ cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho *
        (cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by
      simpa only [q] using hradial
    _ ≤ cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho *
        (3 ^ (1 - (-1 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m) :=
      mul_le_mul_of_nonneg_left hredistribute hconstant
    _ = cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
      rw [cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft]
      ring

/-- Literal phased noncentral part of the stabilized Green numerator. -/
def cmp89Eq248ComplexFineLatticePhasedNoncentralGreenSum_draft
    (L j : ℕ) (mass : ℝ) (z : Fin 4 → ℂ)
    (endpointDisplacement : Fin 4 → ℝ) : ℂ :=
  ∑ m ∈ (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
      (cmp89Eq249ZeroAlias 4),
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement) *
      (cmp89Eq245EntireAverageAmplitude 4 (L ^ j)
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m))

/-- Explicit bound for the complete phased noncentral Green sum. -/
def cmp89Eq248ComplexNoncentralGreenSumBound_draft (rho : ℝ) : ℝ :=
  cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
    (∑' n : ℤ,
      cmp89Eq251OneDimensionalAliasWeight
        (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4

/-- Every real alias has the same signed-contour phase norm, while the
phase itself remains inside the finite sum. -/
theorem norm_cmp89Eq248ComplexFineLatticePhasedNoncentralGreenSum_signedContour_le_draft
    {L j : ℕ} [NeZero L] {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (endpointDisplacement : Fin 4 → ℝ)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq248ComplexFineLatticePhasedNoncentralGreenSum_draft L j mass
        (cmp89Eq251SignedContourMomentum rho p endpointDisplacement)
        endpointDisplacement‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement)) *
        cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
  let N : ℕ := L ^ j
  let aliases := cmp89Eq245CenteredAliasVectors 4 N
  let zeroAlias := cmp89Eq249ZeroAlias 4
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p endpointDisplacement
  let quotient : (Fin 4 → ℤ) → ℂ := fun m =>
    cmp89Eq245EntireAverageAmplitude 4 N
        (cmp89Eq248EntireAliasMomentum z m) /
      cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
        (cmp89Eq248EntireAliasMomentum z m)
  let weight : (Fin 4 → ℤ) → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 (-1)) m
  let decay :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement))
  have hN : 0 < N :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p endpointDisplacement nu
  have hdecay : 0 ≤ decay := (Real.exp_pos _).le
  have hconstant :
      0 ≤ cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho := by
    rw [cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
      cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hpointwise :
      ∀ m ∈ aliases.erase zeroAlias,
        ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
              (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement) *
            quotient m‖ ≤
          decay *
            (cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
              weight m) := by
    intro m hm
    have hmParts := Finset.mem_erase.mp hm
    have hm0 : m ≠ 0 := by
      simpa only [zeroAlias, cmp89Eq249ZeroAlias] using hmParts.1
    have hquotient :=
      norm_cmp89Eq248ComplexNoncentralGreenQuotient_le_sourceWeight_draft
        (mass := mass) hN hrho hradius hmParts.2 hm0 hp hreal himag
        hamplitude
    have hphase :
        ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement)‖ =
          decay := by
      simpa [z, decay] using
        (norm_exp_I_cmp89Eq251EntireAliasPhase_signedContour
          rho p endpointDisplacement m)
    rw [norm_mul, hphase]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [quotient, weight, N, Nat.cast_pow] using hquotient)
      hdecay
  have heraseWeight :
      (∑ m ∈ aliases.erase zeroAlias, weight m) ≤
        ∑ m ∈ aliases, weight m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset zeroAlias aliases)
      (fun m _ _ =>
        cmp89Eq251MultidimensionalAliasWeight_nonneg
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m)
  have hseries :
      (∑ m ∈ aliases, weight m) ≤
        (∑' n : ℤ,
          cmp89Eq251OneDimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4 := by
    simpa only [aliases, weight, N] using
      (cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
        (d := 4) N (alpha := (-1 : ℝ)) (by norm_num) (by norm_num))
  rw [cmp89Eq248ComplexFineLatticePhasedNoncentralGreenSum_draft,
    cmp89Eq248ComplexNoncentralGreenSumBound_draft]
  change ‖∑ m ∈ aliases.erase zeroAlias,
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement) *
        quotient m‖ ≤ _
  calc
    _ ≤ ∑ m ∈ aliases.erase zeroAlias,
        ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
              (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement) *
            quotient m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ aliases.erase zeroAlias,
        decay *
          (cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
            weight m) := Finset.sum_le_sum hpointwise
    _ = decay *
        (cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
          ∑ m ∈ aliases.erase zeroAlias, weight m) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ decay *
        (cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
          ∑ m ∈ aliases, weight m) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left heraseWeight hconstant) hdecay
    _ ≤ decay *
        (cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
          (∑' n : ℤ,
            cmp89Eq251OneDimensionalAliasWeight
              (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseries hconstant) hdecay

/-- The complete Green numerator bound keeps the central fine-symbol factor
and the reciprocal-alias sum visible. -/
def cmp89Eq248ComplexGreenNumeratorBound_draft (rho : ℝ) : ℝ :=
  Real.exp rho ^ 4 +
    cmp89Eq251CentralFineSymbolStripUpperBound rho *
      cmp89Eq248ComplexNoncentralGreenSumBound_draft rho

/-- Exact central/noncentral decomposition of the stabilized Green numerator,
with every noncentral phase retained inside the sum. -/
theorem cmp89Eq248ComplexStabilizedGreenEndpointNumerator_eq_phased_draft
    {L j : ℕ} {mass : ℝ} (z : Fin 4 → ℂ)
    (endpointDisplacement : Fin 4 → ℝ) :
    cmp89Eq248ComplexStabilizedGreenEndpointNumerator 4 L j mass z
        endpointDisplacement =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase z endpointDisplacement) *
          cmp89Eq245EntireAverageAmplitude 4 (L ^ j) z +
        cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
          cmp89Eq248ComplexFineLatticePhasedNoncentralGreenSum_draft
            L j mass z endpointDisplacement := by
  unfold cmp89Eq248ComplexStabilizedGreenEndpointNumerator
    cmp89Eq248ComplexBareGreenEndpointNumerator
    cmp89Eq248ComplexFineLatticePhasedNoncentralGreenSum_draft
  rw [cmp89Eq248EntireAliasMomentum_zero]
  simp [div_eq_mul_inv, mul_assoc]

/-- The complete stabilized Green numerator has the exact signed physical
endpoint decay, uniformly in the mass window. -/
theorem norm_cmp89Eq248ComplexStabilizedGreenEndpointNumerator_signedContour_le_draft
    {L j : ℕ} [NeZero L] {mass rho : ℝ}
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (endpointDisplacement : Fin 4 → ℝ)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq248ComplexStabilizedGreenEndpointNumerator 4 L j mass
        (cmp89Eq251SignedContourMomentum rho p endpointDisplacement)
        endpointDisplacement‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement)) *
        cmp89Eq248ComplexGreenNumeratorBound_draft rho := by
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p endpointDisplacement
  let decay : ℝ :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement))
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p endpointDisplacement nu
  have hdecay : 0 ≤ decay := (Real.exp_pos _).le
  have hphase :
      ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z
        endpointDisplacement)‖ = decay := by
    simpa [z, decay, cmp89Eq248EntireAliasMomentum_zero] using
      (norm_exp_I_cmp89Eq251EntireAliasPhase_signedContour
        rho p endpointDisplacement (cmp89Eq249ZeroAlias 4))
  have havg :=
    norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow
      (N := L ^ j) (z := z) (rho := rho)
      (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j) hrho himag
  have hcentral :
      ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z
            endpointDisplacement) *
          cmp89Eq245EntireAverageAmplitude 4 (L ^ j) z‖ ≤
        decay * Real.exp rho ^ 4 := by
    rw [norm_mul, hphase]
    exact mul_le_mul_of_nonneg_left havg hdecay
  have hfine :=
    norm_cmp89Eq249CentralEntireFineSymbol_le_stripUpperBound
      (L := L) (j := j) hmass hrho hp hreal himag
  have hsum :=
    norm_cmp89Eq248ComplexFineLatticePhasedNoncentralGreenSum_signedContour_le_draft
      (L := L) (j := j) (mass := mass) hrho hradius hp
      endpointDisplacement hamplitude
  have hfineNonneg :
      0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
    rw [cmp89Eq251CentralFineSymbolStripUpperBound,
      cmp89Eq249CentralFineSymbolVerticalBound,
      cmp89Eq249CentralFineSymbolRealBound]
    positivity
  have hnoncentral :
      ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
          cmp89Eq248ComplexFineLatticePhasedNoncentralGreenSum_draft
            L j mass z endpointDisplacement‖ ≤
        decay *
          (cmp89Eq251CentralFineSymbolStripUpperBound rho *
            cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) := by
    rw [norm_mul]
    have hmul :=
      mul_le_mul hfine hsum (norm_nonneg _) hfineNonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  rw [cmp89Eq248ComplexStabilizedGreenEndpointNumerator_eq_phased_draft]
  calc
    ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z
          endpointDisplacement) *
        cmp89Eq245EntireAverageAmplitude 4 (L ^ j) z +
      cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
        cmp89Eq248ComplexFineLatticePhasedNoncentralGreenSum_draft
          L j mass z endpointDisplacement‖ ≤
        ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z
            endpointDisplacement) *
          cmp89Eq245EntireAverageAmplitude 4 (L ^ j) z‖ +
        ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
          cmp89Eq248ComplexFineLatticePhasedNoncentralGreenSum_draft
            L j mass z endpointDisplacement‖ := norm_add_le _ _
    _ ≤ decay * Real.exp rho ^ 4 +
        decay *
          (cmp89Eq251CentralFineSymbolStripUpperBound rho *
            cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) :=
      add_le_add hcentral hnoncentral
    _ = decay * cmp89Eq248ComplexGreenNumeratorBound_draft rho := by
      rw [cmp89Eq248ComplexGreenNumeratorBound_draft]
      ring

/-- Explicit mass-uniform pointwise Green-integrand majorant. -/
def cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
    (a rho : ℝ) : ℝ :=
  cmp89Eq248ComplexGreenNumeratorBound_draft rho *
    cmp89Eq249CentralStabilizedComplexReciprocalBound a rho

/-- Pointwise Green-integrand decay on the signed physical contour, with no
strictly-positive-mass premise. -/
theorem norm_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_signedContour_le_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmass : CMP89Eq251UniformMassWindow mass)
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (endpointDisplacement : Fin 4 → ℝ) :
    ‖cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
        (cmp89Eq251SignedContourMomentum rho p endpointDisplacement)
        endpointDisplacement‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement)) *
        cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho := by
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p endpointDisplacement
  let decay : ℝ :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement))
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p endpointDisplacement nu
  have hnum :=
    norm_cmp89Eq248ComplexStabilizedGreenEndpointNumerator_signedContour_le_draft
      (L := L) (j := j) (mass := mass) hmass hrho hradius hp
      endpointDisplacement hamplitude
  have hrecip :=
    norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le_massUniform
      (L := L) (j := j) (mass := mass) ha hrho hradius hmass hwindow
      hp hreal himag hamplitude
  have hdecay : 0 ≤ decay := (Real.exp_pos _).le
  have hnumBoundNonneg :
      0 ≤ decay * cmp89Eq248ComplexGreenNumeratorBound_draft rho := by
    refine mul_nonneg hdecay ?_
    rw [cmp89Eq248ComplexGreenNumeratorBound_draft]
    have hfine :
        0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
      rw [cmp89Eq251CentralFineSymbolStripUpperBound,
        cmp89Eq249CentralFineSymbolVerticalBound,
        cmp89Eq249CentralFineSymbolRealBound]
      positivity
    have hsum :
        0 ≤ cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
      rw [cmp89Eq248ComplexNoncentralGreenSumBound_draft,
        cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
        cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
        cmp89Eq245EntireAverageAliasStripConstant]
      positivity
    exact add_nonneg (by positivity) (mul_nonneg hfine hsum)
  rw [cmp89Eq248ComplexStabilizedGreenEndpointIntegrand, div_eq_mul_inv,
    norm_mul, cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft]
  have hmul := mul_le_mul hnum hrecip (norm_nonneg _) hnumBoundNonneg
  simpa [z, decay, mul_assoc] using hmul

end

end YangMills.RG
