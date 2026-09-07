import YangMills.RG.BalabanCMP89Eq246FinePointSourceHolomorphy

/-!
# Constructed domain for the complete CMP89 (2.46) alias solver

The explicit finite solver needs three literal nonvanishing facts.  This
package names those facts, while `of_commonRadius` constructs all three from
the already sealed common-polistrip windows.  Callers do not get to supply an
arbitrary solved Green or an inverse equality.
-/

namespace YangMills.RG

noncomputable section

/-- The exact nonvanishing domain consumed by the stabilized full solution. -/
structure CMP89Eq246FullSolutionDomain
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ) : Prop where
  fine : ∀ m : CMP89Eq246AliasIndex d L j,
    m ≠ cmp89Eq249CentralAliasIndex d L j →
      cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0
  stabilized :
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0
  row : cmp89Eq246EntireAliasAverageRow d L j z
    (cmp89Eq249CentralAliasIndex d L j) ≠ 0

/-- The physical four-dimensional common-radius hypotheses construct the
complete finite-solver domain; the domain is not an input in this theorem. -/
theorem cmp89Eq246FullSolutionDomain_of_commonRadius
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    CMP89Eq246FullSolutionDomain 4 L j mass a z := by
  have hfine : ∀ m : CMP89Eq246AliasIndex 4 L j,
      m ≠ cmp89Eq249CentralAliasIndex 4 L j →
        cmp89Eq246EntireAliasFineSymbol 4 L j mass z m ≠ 0 := by
    intro m hm
    have hm0 : m.1 ≠ cmp89Eq249ZeroAlias 4 := by
      intro hm0
      apply hm
      apply Subtype.ext
      exact hm0
    have hmErase :
        m.1 ∈ (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
          (cmp89Eq249ZeroAlias 4) := Finset.mem_erase.mpr ⟨hm0, m.2⟩
    exact cmp89Eq251NoncentralFineSymbol_ne_zero_of_commonRadius
      hrho hradius hmErase hp hreal himag
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z ≠ 0 :=
    cmp89Eq249CentralStabilizedAliasDenominator_ne_zero
      ha hmassPos hrho hradius hmass hdenWindow hp hreal himag hamplitude
  have hpair : cmp89Eq249CentralEntireAveragePair 4 L j z ≠ 0 :=
    cmp89Eq249CentralEntireAveragePair_ne_zero
      hrho hpairWindow hp hreal himag
  exact ⟨hfine, hstabilized,
    cmp89Eq246CentralAverageRow_ne_zero_of_pair_ne_zero 4 L j z hpair⟩

end

end YangMills.RG
