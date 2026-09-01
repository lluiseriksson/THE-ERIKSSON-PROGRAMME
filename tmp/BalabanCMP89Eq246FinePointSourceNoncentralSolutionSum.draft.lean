import YangMills.RG.BalabanCMP89Eq246FinePointSourceBareDiagonalSum
import YangMills.RG.BalabanCMP89Eq246FinePointSourceNoncentralCorrectionSum

/-!
# Draft: complete noncentral fine-point-source solution sum

This leaf recombines the two branches only after their different scaling has
been exposed: the bare diagonal contribution is quadratic in the finite alias
side length, while the rank-one correction is scale-uniform.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit budget for the complete noncentral solution sum. -/
def cmp89Eq246FinePointSourceNoncentralSolutionSumBound
    (L j : ℕ) (a rho : ℝ) (sourceEndpoint : Fin 4 → ℝ) : ℝ :=
  cmp89Eq246FinePointSourceBareDiagonalSumBound L j rho sourceEndpoint +
    cmp89Eq246FinePointSourceNoncentralCorrectionSumBound
      a rho sourceEndpoint

/-- The complete noncentral branch is the sum of the visible quadratic bare
budget and the uniformly summable rank-one correction. -/
theorem sum_norm_cmp89Eq246FinePointSourceNoncentralSolution_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (sourceEndpoint : Fin 4 → ℝ) :
    (∑ m ∈ (Finset.univ : Finset (CMP89Eq246AliasIndex 4 L j)).erase
        (cmp89Eq249CentralAliasIndex 4 L j),
      ‖cmp89Eq246StabilizedFinePointSourceSolution
        4 L j mass a z sourceEndpoint m‖) ≤
      cmp89Eq246FinePointSourceNoncentralSolutionSumBound
        L j a rho sourceEndpoint := by
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let source :=
    cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint
  let moment :=
    cmp89Eq246StabilizedFinePointSourceSolutionMoment
      4 L j mass a sourceEndpoint z
  let bare : CMP89Eq246AliasIndex 4 L j → ℂ := fun m =>
    source m / cmp89Eq246EntireAliasFineSymbol 4 L j mass z m
  let correction : CMP89Eq246AliasIndex 4 L j → ℂ := fun m =>
    (a : ℂ) * cmp89Eq246EntireAliasAverageColumn 4 L j z m * moment /
      cmp89Eq246EntireAliasFineSymbol 4 L j mass z m
  have hbranch : ∀ m ∈ (Finset.univ :
      Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
      cmp89Eq246StabilizedFinePointSourceSolution
          4 L j mass a z sourceEndpoint m = bare m - correction m := by
    intro m hm
    have hmne : m ≠ central := (Finset.mem_erase.mp hm).1
    simp [cmp89Eq246StabilizedFinePointSourceSolution,
      cmp89Eq246StabilizedAliasFullSolution, central, source, moment,
      bare, correction, hmne,
      cmp89Eq246StabilizedFinePointSourceSolutionMoment_eq]
  have hsplit :
      (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        ‖cmp89Eq246StabilizedFinePointSourceSolution
          4 L j mass a z sourceEndpoint m‖) ≤
        (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
          ‖bare m‖) +
        (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
          ‖correction m‖) := by
    calc
      _ = ∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
          ‖bare m - correction m‖ := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [hbranch m hm]
      _ ≤ ∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
          (‖bare m‖ + ‖correction m‖) := by
        exact Finset.sum_le_sum fun m _ => norm_sub_le (bare m) (correction m)
      _ = _ := Finset.sum_add_distrib
  have hbare :=
    sum_norm_cmp89Eq246FinePointSourceBareDiagonal_le
      (L := L) (j := j) (mass := mass) (rho := rho)
      hrho hradius hamplitude hp hreal himag sourceEndpoint
  have hcorrection :=
    sum_norm_cmp89Eq246FinePointSourceNoncentralCorrection_le
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hradius hmass hwindow hamplitude hp hreal himag sourceEndpoint
  exact hsplit.trans (by
    simpa [bare, correction,
      cmp89Eq246FinePointSourceNoncentralSolutionSumBound,
      cmp89Eq246FinePointSourceBareDiagonalSumBound,
      cmp89Eq246FinePointSourceNoncentralCorrectionSumBound,
      source, moment] using add_le_add hbare hcorrection)

end

end YangMills.RG
