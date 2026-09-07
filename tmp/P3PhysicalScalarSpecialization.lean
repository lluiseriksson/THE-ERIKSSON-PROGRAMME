import tmp.P3SourceStepCoisometry

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only physical index/spacing dictionary for P3.

The source index shift is explicit: a current positive step with value `k`
uses recurrence index `k-1`, while its next prefix uses recurrence index
`k`.  This file is not compiler evidence and is not imported by the tracked
tree.
-/

namespace YangMills.RG

noncomputable section

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Positive prefix immediately after a positive coarse step. -/
def ScratchCMP85PositiveCoarseStep.nextPrefix
    (k : ScratchCMP85PositiveCoarseStep depth) :
    ScratchCMP85PositivePrefix depth :=
  ⟨k.1.succ, Nat.succ_pos k.1.val⟩

/-- The abstract `b` is exactly the current printed source coefficient. -/
theorem scratch_cmp85RecurrenceB_eq_sourceCurrentWeighted
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (a : ℝ) (k : ScratchCMP85PositiveCoarseStep depth) :
    scratch_cmp85RecurrenceB a (M : ℝ)
        (T.towerAt k.currentPrefix.1).terminalSpacing (k.1.val - 1) =
      scratch_cmp85SourcePrefixWeightedCoefficient T a k.currentPrefix := by
  rfl

/-- The abstract `c` uses the literal spacing of the next retained prefix. -/
theorem scratch_cmp85RecurrenceC_eq_sourceStepWeighted
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (a : ℝ) (k : ScratchCMP85PositiveCoarseStep depth) :
    scratch_cmp85RecurrenceC a (M : ℝ)
        (T.towerAt k.currentPrefix.1).terminalSpacing =
      scratch_cmp85SourceStepWeightedCoefficient T a k.1 := by
  have hterminal :
      (T.towerAt k.1.succ).terminalSpacing =
        (M : ℝ) * (T.towerAt k.currentPrefix.1).terminalSpacing := by
    rw [T.towerAt_terminalSpacing, T.towerAt_terminalSpacing]
    simp only [ScratchCMP85PositiveCoarseStep.currentPrefix,
      Fin.val_succ, Fin.val_castSucc]
    rw [pow_succ]
    ring
  unfold scratch_cmp85RecurrenceC
  unfold scratch_cmp85SourceStepWeightedCoefficient
  rw [hterminal]

/-- The abstract `beta` is exactly the printed coefficient of the next
positive prefix; the `k-1`/`k` source shift is proved, not inferred. -/
theorem scratch_cmp85RecurrenceBeta_eq_sourceNextWeighted
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (a : ℝ) (k : ScratchCMP85PositiveCoarseStep depth) :
    scratch_cmp85RecurrenceBeta a (M : ℝ)
        (T.towerAt k.currentPrefix.1).terminalSpacing (k.1.val - 1) =
      scratch_cmp85SourcePrefixWeightedCoefficient T a k.nextPrefix := by
  have hindex : (k.1.val - 1) + 1 = k.1.val := by omega
  have hnextIndex : k.nextPrefix.1.val - 1 = k.1.val := by
    simp only [ScratchCMP85PositiveCoarseStep.nextPrefix, Fin.val_succ]
    omega
  have hterminal :
      (T.towerAt k.nextPrefix.1).terminalSpacing =
        (M : ℝ) * (T.towerAt k.currentPrefix.1).terminalSpacing := by
    rw [T.towerAt_terminalSpacing, T.towerAt_terminalSpacing]
    simp only [ScratchCMP85PositiveCoarseStep.nextPrefix,
      ScratchCMP85PositiveCoarseStep.currentPrefix,
      Fin.val_succ, Fin.val_castSucc]
    rw [pow_succ]
    ring
  unfold scratch_cmp85RecurrenceBeta
  unfold scratch_cmp85SourcePrefixWeightedCoefficient
  unfold scratch_cmp85SourcePrefixA
  rw [hindex, hnextIndex, hterminal]

end

end YangMills.RG
