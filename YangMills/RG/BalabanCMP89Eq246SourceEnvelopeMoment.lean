import YangMills.RG.BalabanCMP89Eq246FinePointSourceMomentBound

/-!
# Cold-sealed: common source-envelope transport below CMP89 (2.46)

Cold compiler validation: exact source checkpoint
`06e6be132c5e7742bb60102e890814d4961b5d2a` passed the fresh Colab Pro+
CPU/high-RAM focal and exact axiom gate recorded in Verification Ledger
Addendum 1031.

The absolute point-source strip bound is too coarse for the later relative
endpoint contour.  This draft isolates the actual input used by the moment
estimates: one nonnegative scalar `g` bounding every alias component of an
arbitrary source.  Keeping `g` abstract allows the physical specialization
to use the directed signed-contour source factor.

The two theorems below transport the same `g` through the noncentral row
moment and the exact stabilized solution moment.  They neither choose the
physical source nor claim endpoint decay.
-/

namespace YangMills.RG

noncomputable section

/-- The noncentral row moment only consumes a common pointwise source
envelope; no absolute physical endpoint norm is required. -/
theorem norm_cmp89Eq246StabilizedAliasNoncentralSourceMoment_le_of_envelope
    {L j : ℕ} [NeZero L] {mass rho g : ℝ}
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (source : CMP89Eq246AliasIndex 4 L j → ℂ)
    (hg : 0 ≤ g) (hsource : ∀ n, ‖source n‖ ≤ g) :
    ‖cmp89Eq246StabilizedAliasNoncentralSourceMoment
        4 L j mass z source‖ ≤
      g * cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
  classical
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let weight : CMP89Eq246AliasIndex 4 L j → ℝ := fun n =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 (-1)) n.1
  let constant := cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho
  have hconstant : 0 ≤ constant := by
    dsimp [constant, cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
      cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hpointwise : ∀ n ∈ Finset.univ.erase central,
      ‖cmp89Eq246EntireAliasAverageRow 4 L j z n * source n /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z n‖ ≤
        g * (constant * weight n) := by
    intro n hn
    have hnc : n ≠ central := (Finset.mem_erase.mp hn).1
    have hm0 : n.1 ≠ cmp89Eq249ZeroAlias 4 := by
      intro hz
      apply hnc
      apply Subtype.ext
      exact hz
    have hquot :=
      norm_cmp89Eq246EntireAliasRowGreenQuotient_le_sourceWeight
        (N := L ^ j)
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
        (mass := mass) hrho hradius n.2 hm0 hp hreal himag hamplitude
    rw [norm_div, norm_mul]
    have hmul := mul_le_mul (hsource n) hquot (norm_nonneg _) hg
    simpa [cmp89Eq246EntireAliasAverageRow,
      cmp89Eq246EntireAliasFineSymbol, weight, constant,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have heraseWeight :
      (∑ n ∈ Finset.univ.erase central, weight n) ≤ ∑ n, weight n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset central Finset.univ)
      (fun n _ _ => cmp89Eq251MultidimensionalAliasWeight_nonneg _ n.1)
  have hsubtype :
      (∑ n : CMP89Eq246AliasIndex 4 L j, weight n) =
        ∑ m ∈ cmp89Eq245CenteredAliasVectors 4 (L ^ j),
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
    rw [Finset.sum_subtype
      (cmp89Eq245CenteredAliasVectors 4 (L ^ j)) (fun _ => Iff.rfl)]
  have hseries :
      (∑ n : CMP89Eq246AliasIndex 4 L j, weight n) ≤
        (∑' n : ℤ, cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4 := by
    rw [hsubtype]
    exact cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
      (d := 4) (L ^ j) (alpha := (-1 : ℝ)) (by norm_num) (by norm_num)
  rw [cmp89Eq246StabilizedAliasNoncentralSourceMoment]
  calc
    ‖∑ n ∈ Finset.univ.erase central,
        cmp89Eq246EntireAliasAverageRow 4 L j z n * source n /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z n‖ ≤
      ∑ n ∈ Finset.univ.erase central,
        ‖cmp89Eq246EntireAliasAverageRow 4 L j z n * source n /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.univ.erase central,
        g * (constant * weight n) := Finset.sum_le_sum hpointwise
    _ = g * (constant *
        ∑ n ∈ Finset.univ.erase central, weight n) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ g * (constant * ∑ n, weight n) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left heraseWeight hconstant) hg
    _ ≤ g * (constant *
        (∑' n : ℤ, cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseries hconstant) hg
    _ = g * cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
      rw [cmp89Eq248ComplexNoncentralGreenSumBound_draft]

/-- The exact stabilized solution moment preserves the same common source
envelope and introduces no alias-cardinality loss. -/
theorem norm_cmp89Eq246StabilizedAliasFullSolutionMoment_le_of_envelope
    {L j : ℕ} [NeZero L] {mass a rho g : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (source : CMP89Eq246AliasIndex 4 L j → ℂ)
    (hg : 0 ≤ g) (hsource : ∀ n, ‖source n‖ ≤ g) :
    ‖cmp89Eq246StabilizedAliasFullSolutionMoment
        4 L j mass a z source‖ ≤
      g * cmp89Eq246FinePointSourceMomentAmplitudeBound a rho := by
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let base := cmp89Eq246StabilizedAliasNoncentralSourceMoment
    4 L j mass z source
  have hrow :
      ‖cmp89Eq246EntireAliasAverageRow 4 L j z central‖ ≤
        Real.exp rho ^ 4 := by
    simpa [central, cmp89Eq246EntireAliasAverageRow,
      cmp89Eq248EntireAliasMomentum_zero] using
      (norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow
        (d := 4) (N := L ^ j)
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
        hrho (fun mu => by simpa using himag mu))
  have hcentral : ‖cmp89Eq246EntireAliasAverageRow 4 L j z central *
      source central‖ ≤ g * Real.exp rho ^ 4 := by
    rw [norm_mul]
    have hmul := mul_le_mul hrow (hsource central) (norm_nonneg _)
      (by positivity : 0 ≤ Real.exp rho ^ 4)
    simpa [mul_comm] using hmul
  have hfine :=
    norm_cmp89Eq249CentralEntireFineSymbol_le_stripUpperBound
      (L := L) (j := j) hmass hrho hp hreal himag
  have hbase :
      ‖base‖ ≤ g *
        cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
    simpa [base] using
      norm_cmp89Eq246StabilizedAliasNoncentralSourceMoment_le_of_envelope
        (L := L) (j := j) (mass := mass) hrho hradius hp hreal himag
        hamplitude source hg hsource
  have hfineNonneg :
      0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
    rw [cmp89Eq251CentralFineSymbolStripUpperBound,
      cmp89Eq249CentralFineSymbolVerticalBound,
      cmp89Eq249CentralFineSymbolRealBound]
    positivity
  have hnoncentral :
      ‖cmp89Eq246EntireAliasFineSymbol 4 L j mass z central * base‖ ≤
        g * (cmp89Eq251CentralFineSymbolStripUpperBound rho *
          cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) := by
    have hcentralFine :
        cmp89Eq246EntireAliasFineSymbol 4 L j mass z central =
          cmp89Eq249CentralEntireFineSymbol 4 L j mass z := by
      simp [central, cmp89Eq246EntireAliasFineSymbol,
        cmp89Eq249CentralEntireFineSymbol,
        cmp89Eq248EntireAliasMomentum_zero]
    rw [norm_mul, hcentralFine]
    have hmul := mul_le_mul hfine hbase (norm_nonneg _) hfineNonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hnum :
      ‖cmp89Eq246EntireAliasAverageRow 4 L j z central * source central +
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z central * base‖ ≤
        g * (Real.exp rho ^ 4 +
          cmp89Eq251CentralFineSymbolStripUpperBound rho *
            cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) := by
    calc
      _ ≤ ‖cmp89Eq246EntireAliasAverageRow 4 L j z central * source central‖ +
          ‖cmp89Eq246EntireAliasFineSymbol 4 L j mass z central * base‖ :=
        norm_add_le _ _
      _ ≤ g * Real.exp rho ^ 4 +
          g * (cmp89Eq251CentralFineSymbolStripUpperBound rho *
            cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) :=
        add_le_add hcentral hnoncentral
      _ = _ := by ring
  have hrecip :=
    norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le_massUniform
      (L := L) (j := j) (mass := mass) ha hrho hradius hmass hwindow
      hp hreal himag hamplitude
  have hnumNonneg :
      0 ≤ g * (Real.exp rho ^ 4 +
        cmp89Eq251CentralFineSymbolStripUpperBound rho *
          cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) := by
    refine mul_nonneg hg (add_nonneg (by positivity) ?_)
    have hsum : 0 ≤ cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
      rw [cmp89Eq248ComplexNoncentralGreenSumBound_draft,
        cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
        cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
        cmp89Eq245EntireAverageAliasStripConstant]
      positivity
    exact mul_nonneg hfineNonneg hsum
  rw [cmp89Eq246StabilizedAliasFullSolutionMoment, norm_div,
    div_eq_mul_inv, cmp89Eq246FinePointSourceMomentAmplitudeBound]
  have hmul := mul_le_mul hnum hrecip (norm_nonneg _) hnumNonneg
  simpa [central, base, mul_assoc] using hmul

end

end YangMills.RG
