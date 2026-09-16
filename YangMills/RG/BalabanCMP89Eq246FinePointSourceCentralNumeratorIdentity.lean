import YangMills.RG.BalabanCMP89Eq246FinePointSourceMomentBound
import YangMills.RG.BalabanCMP89Eq249StabilizedAliasTransposeSolution

/-!
# Cold-sealed: exact numerator identity for the central Eq. (2.46) component

Cold compiler validation: exact source checkpoint
`c1cdd849d0117cdf18724ac076cd4a5bbfd67b35` passed the fresh Colab Pro+
CPU/high-RAM focal and exact axiom gate recorded in Verification Ledger
Addendum 1027.

The row factor must remain inside the noncentral sum until the literal
noncentral source moment and the printed row-column alias sum have been
recognized.  This prevents the quadratic bare-diagonal budget from being
charged to the central component.
-/

namespace YangMills.RG

noncomputable section

/-- The central numerator splits into the already named source moment and
the literal noncentral row-column sum. -/
theorem cmp89Eq246FinePointSourceCentralNumerator_eq
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (sourceEndpoint : Fin 4 → ℝ) (z : Fin 4 → ℂ) :
    let central := cmp89Eq249CentralAliasIndex 4 L j
    let source :=
      cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint
    let moment :=
      cmp89Eq246StabilizedFinePointSourceSolutionMoment
        4 L j mass a sourceEndpoint z
    let row := cmp89Eq246EntireAliasAverageRow 4 L j z
    let column := cmp89Eq246EntireAliasAverageColumn 4 L j z
    let fine := cmp89Eq246EntireAliasFineSymbol 4 L j mass z
    moment - ∑ n ∈ Finset.univ.erase central,
        row n * (source n / fine n -
          (a : ℂ) * column n * moment / fine n) =
      moment -
        cmp89Eq246StabilizedAliasNoncentralSourceMoment
          4 L j mass z source +
        (a : ℂ) * moment *
          cmp89Eq249ComplexNoncentralAliasSum 4 L j mass z := by
  dsimp only
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let source :=
    cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint
  let moment :=
    cmp89Eq246StabilizedFinePointSourceSolutionMoment
      4 L j mass a sourceEndpoint z
  let row := cmp89Eq246EntireAliasAverageRow 4 L j z
  let column := cmp89Eq246EntireAliasAverageColumn 4 L j z
  let fine := cmp89Eq246EntireAliasFineSymbol 4 L j mass z
  let sourceMoment :=
    cmp89Eq246StabilizedAliasNoncentralSourceMoment
      4 L j mass z source
  let aliasSum := cmp89Eq249ComplexNoncentralAliasSum 4 L j mass z
  have hsource :
      (∑ n ∈ Finset.univ.erase central,
        row n * (source n / fine n)) = sourceMoment := by
    dsimp only [sourceMoment,
      cmp89Eq246StabilizedAliasNoncentralSourceMoment]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hcorrection :
      (∑ n ∈ Finset.univ.erase central,
        row n * ((a : ℂ) * column n * moment / fine n)) =
          (a : ℂ) * moment * aliasSum := by
    dsimp only [aliasSum]
    rw [← cmp89Eq249AliasSubtypeNoncentralSum_eq
      (d := 4) (L := L) (j := j) mass z]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [row, column, fine]
    ring
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hsource, hcorrection]
  ring

end

end YangMills.RG
