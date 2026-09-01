import YangMills.RG.BalabanCMP89Eq246FinePointSourceBareDiagonalBound
import YangMills.RG.BalabanCMP89Eq251CenteredHalfAliasSum

/-!
# Draft: finite sum of the bare diagonal branch below CMP89 (2.46)

This is the quantitative endpoint forced by the unsmoothed fine-point source:
the rank-one correction is uniformly summable, whereas the literal diagonal
inverse carries a visible `O((L^j + 1)^2)` four-dimensional value scale.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit finite-volume budget for the complete noncentral bare diagonal
sum. -/
def cmp89Eq246FinePointSourceBareDiagonalSumBound
    (L j : ℕ) (rho : ℝ) (sourceEndpoint : Fin 4 → ℝ) : ℝ :=
  cmp89Eq251ContourPhaseGrowth rho sourceEndpoint *
    (cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
      (256 * ((L ^ j + 1 : ℕ) : ℝ) ^ 2))

/-- Summing the literal bare diagonal solution over the finite alias fibre
costs exactly the quadratic four-dimensional half-weight budget. -/
theorem sum_norm_cmp89Eq246FinePointSourceBareDiagonal_le
    {L j : ℕ} [NeZero L] {mass rho : ℝ}
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (sourceEndpoint : Fin 4 → ℝ) :
    (∑ m ∈ (Finset.univ : Finset (CMP89Eq246AliasIndex 4 L j)).erase
        (cmp89Eq249CentralAliasIndex 4 L j),
      ‖cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint m /
        cmp89Eq246EntireAliasFineSymbol 4 L j mass z m‖) ≤
      cmp89Eq246FinePointSourceBareDiagonalSumBound
        L j rho sourceEndpoint := by
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let growth := cmp89Eq251ContourPhaseGrowth rho sourceEndpoint
  let amplitude := cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound
  let weight : CMP89Eq246AliasIndex 4 L j → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m.1
  have hgrowth : 0 ≤ growth := by
    dsimp [growth, cmp89Eq251ContourPhaseGrowth]
    positivity
  have hamplitudeNonneg : 0 ≤ amplitude := by
    dsimp [amplitude, cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound]
    positivity
  have hpoint : ∀ m ∈ (Finset.univ :
      Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
      ‖cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint m /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z m‖ ≤
        growth * (amplitude * weight m) := by
    intro m hm
    have hmne : m ≠ central := (Finset.mem_erase.mp hm).1
    simpa [central, growth, amplitude, weight] using
      norm_cmp89Eq246FinePointSourceBareDiagonal_le
        (L := L) (j := j) (mass := mass) (rho := rho)
        hrho hradius hamplitude hp hreal himag sourceEndpoint m hmne
  have heraseWeight :
      (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central, weight m) ≤
        ∑ m, weight m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset central Finset.univ)
      (fun m _ _ => cmp89Eq251MultidimensionalAliasWeight_nonneg _ m.1)
  have hsubtype :
      (∑ m : CMP89Eq246AliasIndex 4 L j, weight m) =
        cmp89Eq251CenteredMultidimensionalAliasSum 4 (L ^ j)
          (1 / 2 : ℝ) := by
    simp [weight, CMP89Eq246AliasIndex,
      cmp89Eq251CenteredMultidimensionalAliasSum]
  have hseries :=
    cmp89Eq251CenteredFourDimensionalAliasSum_half_le (L ^ j)
  calc
    _ ≤ ∑ m ∈ (Finset.univ :
        Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        growth * (amplitude * weight m) :=
      Finset.sum_le_sum hpoint
    _ = growth * (amplitude *
        (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
          weight m)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ growth * (amplitude * ∑ m, weight m) := by
      gcongr
    _ = growth * (amplitude *
        cmp89Eq251CenteredMultidimensionalAliasSum 4 (L ^ j)
          (1 / 2 : ℝ)) := by rw [hsubtype]
    _ ≤ growth * (amplitude *
        (256 * ((L ^ j + 1 : ℕ) : ℝ) ^ 2)) := by
      gcongr
      simpa only [Nat.cast_add, Nat.cast_one] using hseries
    _ = cmp89Eq246FinePointSourceBareDiagonalSumBound
        L j rho sourceEndpoint := by
      rfl

end

end YangMills.RG
