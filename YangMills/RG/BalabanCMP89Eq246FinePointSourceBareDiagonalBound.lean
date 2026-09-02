import YangMills.RG.BalabanCMP89Eq246FinePointSourceMomentBound
import YangMills.RG.BalabanCMP89Eq251BareInverseLaplacianHalfWeight

/-!
# PRE-VALIDATION: the bare diagonal branch below CMP89 (2.46)

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

The normalized fine-point source has unit phase modulus.  Away from the
central alias, the complex fine symbol therefore leaves two inverse momentum
powers.  This leaf keeps that visible value scale and redistributes it only
to the finite exponent-`1/2` alias weight; it does not pretend that the bare
branch is uniformly summable in the alias-window cardinality.
-/

namespace YangMills.RG

noncomputable section

/-- Literal coefficient left by the half-gap inverse and the four-dimensional
redistribution constant `3^2`. -/
def cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound : ℝ :=
  18 * (3 * Real.pi) ^ 2

/-- One noncentral bare diagonal component is controlled by the exponent
`1/2` product weight.  Its finite four-dimensional sum is consequently
quadratic in the alias-window side length. -/
theorem norm_cmp89Eq246FinePointSourceBareDiagonal_le
    {L j : ℕ} [NeZero L] {mass rho : ℝ}
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (_hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (sourceEndpoint : Fin 4 → ℝ)
    (m : CMP89Eq246AliasIndex 4 L j)
    (hm : m ≠ cmp89Eq249CentralAliasIndex 4 L j) :
    ‖cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint m /
        cmp89Eq246EntireAliasFineSymbol 4 L j mass z m‖ ≤
      cmp89Eq251ContourPhaseGrowth rho sourceEndpoint *
        (cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
          cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m.1) := by
  have hm0 : m.1 ≠ cmp89Eq249ZeroAlias 4 := by
    intro hz
    apply hm
    apply Subtype.ext
    exact hz
  let q : Fin 4 → ℝ :=
    fun nu => p nu + 2 * Real.pi * (m.1 nu : ℝ)
  let aliasZ : Fin 4 → ℂ := cmp89Eq248EntireAliasMomentum z m.1
  let growth := cmp89Eq251ContourPhaseGrowth rho sourceEndpoint
  let weight := cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m.1
  have haliasReal : ∀ nu, (aliasZ nu).re = q nu := by
    intro nu
    simp [aliasZ, q, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift, hreal nu]
  have haliasImag : ∀ nu, |(aliasZ nu).im| ≤ rho := by
    intro nu
    simpa [aliasZ, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift] using himag nu
  have hsource :
      ‖cmp89Eq246FinePointSourceAliasVector
          4 L j z sourceEndpoint m‖ ≤ growth := by
    simpa [growth] using
      norm_cmp89Eq246FinePointSourceAliasVector_le_growth
        himag sourceEndpoint m
  have hden :
      ((1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q) / 2 ≤
        ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 ((L ^ j : ℝ))⁻¹ mass aliasZ‖ := by
    simpa only [q, Nat.cast_pow] using
      half_momentum_gap_le_norm_cmp89Eq245EntireScaledLaplacianSymbol_of_uniformRadius
        (mass := mass)
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
        hrho hradius m.2 hm0 hp haliasReal haliasImag
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
          4 ((L ^ j : ℝ))⁻¹ mass aliasZ‖⁻¹ ≤
        2 * (3 * Real.pi) ^ 2 *
          cmp89Eq251EuclideanNorm q ^ (-(2 : ℝ)) := by
    have hinv := one_div_le_one_div_of_le hgap hden
    have hpower :
        cmp89Eq251EuclideanNorm q ^ (-(2 : ℝ)) =
          (cmp89Eq251MomentumSquare q)⁻¹ := by
      rw [Real.rpow_neg hqNorm.le, Real.rpow_two,
        sq_cmp89Eq251EuclideanNorm]
    calc
      _ ≤ (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ := by
        simpa [one_div] using hinv
      _ = 2 * (3 * Real.pi) ^ 2 *
          cmp89Eq251EuclideanNorm q ^ (-(2 : ℝ)) := by
        rw [hpower]
        field_simp [Real.pi_ne_zero, ne_of_gt hqSquare]
  have hredistribute :
      cmp89Eq251EuclideanNorm q ^ (-(2 : ℝ)) ≤ 9 * weight := by
    simpa [q, weight] using
      cmp89Eq251BareInverseLaplacian_le_nine_mul_halfWeight hm0 hp
  have hradialNonneg : 0 ≤ 2 * (3 * Real.pi) ^ 2 := by positivity
  have hinverse :
      ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 ((L ^ j : ℝ))⁻¹ mass aliasZ‖⁻¹ ≤
        cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound * weight := by
    calc
      _ ≤ 2 * (3 * Real.pi) ^ 2 *
          cmp89Eq251EuclideanNorm q ^ (-(2 : ℝ)) := hdenInv
      _ ≤ 2 * (3 * Real.pi) ^ 2 * (9 * weight) :=
        mul_le_mul_of_nonneg_left hredistribute hradialNonneg
      _ = cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound * weight := by
        rw [cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound]
        ring
  rw [cmp89Eq246EntireAliasFineSymbol, norm_div,
    div_eq_mul_inv]
  change ‖cmp89Eq246FinePointSourceAliasVector
      4 L j z sourceEndpoint m‖ *
      ‖cmp89Eq245EntireScaledLaplacianSymbol
        4 ((L ^ j : ℝ))⁻¹ mass aliasZ‖⁻¹ ≤ _
  have hgrowthNonneg : 0 ≤ growth := by
    exact (Real.exp_pos _).le
  exact (mul_le_mul hsource hinverse (inv_nonneg.mpr (norm_nonneg _))
    hgrowthNonneg).trans_eq (by
      simp [growth, weight])

end

end YangMills.RG
